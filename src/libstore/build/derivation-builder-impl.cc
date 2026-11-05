#include "build/derivation-builder-impl.hh"
#include "build/derivation-check.hh"
#include "nix/store/globals.hh"
#include "nix/store/local-store.hh"
#include "nix/store/path-references.hh"
#include "nix/store/posix-fs-canonicalise.hh"
#include "nix/store/restricted-store.hh"
#include "nix/util/archive.hh"
#include "nix/util/file-content-address.hh"
#include "nix/util/file-system.hh"
#include "nix/util/git.hh"
#include "nix/util/processes.hh"
#include "nix/util/source-accessor.hh"
#include "nix/util/topo-sort.hh"

namespace nix {

void DerivationBuilderImpl::anchor() {}

class NotDeterministic final : public CloneableError<NotDeterministic, BuildError>
{
    void anchor() override;

public:
    NotDeterministic(auto &&... args)
        : CloneableError(BuildResult::Failure::NotDeterministic, args...)
    {
        isNonDeterministic = true;
    }
};

void NotDeterministic::anchor() {}

static void handleDiffHook(
    const std::filesystem::path & diffHook,
#ifndef _WIN32
    uid_t uid,
    uid_t gid,
#endif
    const std::filesystem::path & tryA,
    const std::filesystem::path & tryB,
    const std::filesystem::path & drvPath,
    const std::filesystem::path & tmpDir)
{
    try {
        auto diffRes = runProgram(
            RunOptions{
                .spawnOptions =
                    {.program = diffHook,
                     .lookupPath = true,
                     .args = {tryA, tryB, drvPath, tmpDir},
#ifndef _WIN32
                     .uid = uid,
                     .gid = gid,
#endif
                     .chdir = "/"},
            });
        if (!statusOk(diffRes.first))
            throw ExecError(diffRes.first, "diff-hook program %s %s", PathFmt(diffHook), statusToString(diffRes.first));

        if (diffRes.second != "")
            printError(chomp(diffRes.second));
    } catch (Error & error) {
        ErrorInfo ei = error.info();
        // FIXME: wrap errors.
        ei.msg = HintFmt("diff hook execution failed: %s", ei.msg.str());
        logError(ei);
    }
}

static void replaceValidPath(const std::filesystem::path & storePath, const std::filesystem::path & tmpPath)
{
    /* We can't atomically replace storePath (the original) with
       tmpPath (the replacement), so we have to move it out of the
       way first.  We'd better not be interrupted here, because if
       we're repairing (say) Glibc, we end up with a broken system. */
    std::filesystem::path oldPath;

    if (pathExists(storePath)) {
        // why do we loop here?
        // although makeTempPath should be unique, we can't
        // guarantee that.
        do {
            oldPath = makeTempPath(storePath, ".old");
            // store paths are often directories so we can't just unlink() it
            // let's make sure the path doesn't exist before we try to use it
        } while (pathExists(oldPath));
        movePath(storePath, oldPath);
    }
    try {
        movePath(tmpPath, storePath);
    } catch (...) {
        try {
            // attempt to recover
            if (!oldPath.empty())
                movePath(oldPath, storePath);
        } catch (...) {
            ignoreExceptionExceptInterrupt();
        }
        throw;
    }
    if (!oldPath.empty())
        deletePath(oldPath);
}

static constexpr std::string_view defaultRelocateScript = R"sh(#!/bin/sh
export LC_ALL=C
target="$1"
old="$2"
new="$3"
if [ -z "$target" ] || [ -z "$old" ] || [ -z "$new" ] || [ "$old" = "$new" ]; then
    exit 0
fi

# 1. Decompress, rewrite, and deterministically recompress gzip files containing old hash
find "$target" -type f -name '*.gz' 2>/dev/null | while IFS= read -r f; do
    if gzip -dc "$f" 2>/dev/null | grep -q "$old" 2>/dev/null; then
        chmod u+w "$(dirname "$f")" "$f" 2>/dev/null || true
        if gzip -dc "$f" 2>/dev/null | sed "s|$old|$new|g" | gzip -n > "$f.tmp"; then
            cat "$f.tmp" > "$f"
        fi
        rm -f "$f.tmp"
    fi
done

# 2. Rewrite regular files containing old hash in-place (preserving permissions)
find "$target" -type f ! -name '*.gz' -exec grep -l "$old" {} + 2>/dev/null | while IFS= read -r f; do
    chmod u+w "$(dirname "$f")" "$f" 2>/dev/null || true
    if sed "s|$old|$new|g" "$f" > "$f.tmp" 2>/dev/null; then
        cat "$f.tmp" > "$f"
    fi
    rm -f "$f.tmp"
done

# 3. Rewrite symlinks whose target contains old hash
find "$target" -type l 2>/dev/null | while IFS= read -r l; do
    lnk=$(readlink "$l" 2>/dev/null) || continue
    case "$lnk" in
        *"$old"*)
            newlnk=$(printf '%s\n' "$lnk" | sed "s|$old|$new|g")
            chmod u+w "$(dirname "$l")" 2>/dev/null || true
            ln -snf "$newlnk" "$l" 2>/dev/null || true
            ;;
    esac
done
)sh";

static constexpr std::string_view defaultHashScript = R"sh(#!/bin/sh
export LC_ALL=C
set -e
if [ "$1" = "--blind-in-place" ]; then
    target="$2"
    old_self="$3"
    blind_self="$4"
    exec "$target/nix-support/relocate.sh" "$target" "$old_self" "$blind_self"
fi

target="${1:-$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)}"
base="${2:-$(basename -- "$target")}"
name="${base#????????????????????????????????-}"
blind="xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx-$name"

tmpdir=$(mktemp -d)
trap 'chmod -R u+w "$tmpdir" 2>/dev/null || true; rm -rf "$tmpdir"' EXIT
cp -a "$target" "$tmpdir/$base"
chmod -R u+w "$tmpdir/$base" 2>/dev/null || true
"$target/nix-support/relocate.sh" "$tmpdir/$base" "$base" "$blind"
"${NIX_HASH_BIN:-nix-hash}" --type sha256 --truncate --base32 "$tmpdir/$base"
)sh";

static void preparePathForRelocation(
    const std::filesystem::path & path,
    std::optional<std::pair<uid_t, gid_t>> owner)
{
    auto st = lstat(path);
#ifndef _WIN32
    if (owner) {
        if (lchown(path.c_str(), owner->first, owner->second) == -1)
            throw SysError("changing owner of %1% for relocation", PathFmt(path));
    }
#endif
    if (!S_ISLNK(st.st_mode)) {
        chmod(path, (st.st_mode & ~S_IFMT) | S_IWUSR);
    }
    if (S_ISDIR(st.st_mode)) {
        for (auto & entry : DirectoryIterator{path})
            preparePathForRelocation(entry.path(), owner);
    }
}

static bool hasGzFiles(const std::filesystem::path & path)
{
    auto st = lstat(path);
    if (S_ISREG(st.st_mode))
        return path.extension() == ".gz";
    if (S_ISDIR(st.st_mode)) {
        for (auto & entry : DirectoryIterator{path})
            if (hasGzFiles(entry.path()))
                return true;
    }
    return false;
}

static void rewritePathInPlace(
    const std::filesystem::path & path,
    std::string_view oldHash,
    std::string_view newHash)
{
    if (oldHash.empty() || oldHash == newHash)
        return;

    auto st = lstat(path);
    if (S_ISLNK(st.st_mode)) {
        auto target = readLink(path).native();
        if (target.find(oldHash) != std::string::npos) {
            auto newTarget = rewriteStrings(target, StringMap{{std::string(oldHash), std::string(newHash)}});
            auto parent = path.parent_path();
            if (!parent.empty()) {
                auto pst = lstat(parent);
                chmod(parent, (pst.st_mode & ~S_IFMT) | S_IWUSR);
            }
            std::filesystem::remove(path);
            createSymlink(newTarget, path);
        }
    } else if (S_ISREG(st.st_mode)) {
        if (path.extension() == ".gz")
            return;
        auto content = readFile(path);
        if (content.find(oldHash) != std::string::npos) {
            auto newContent = rewriteStrings(content, StringMap{{std::string(oldHash), std::string(newHash)}});
            chmod(path, (st.st_mode & ~S_IFMT) | S_IWUSR);
            writeFile(path, newContent, st.st_mode & 07777);
            chmod(path, st.st_mode & 07777);
        }
    } else if (S_ISDIR(st.st_mode)) {
        chmod(path, (st.st_mode & ~S_IFMT) | S_IWUSR);
        std::vector<std::filesystem::path> children;
        for (auto & entry : DirectoryIterator{path})
            children.push_back(entry.path());
        for (auto & child : children)
            rewritePathInPlace(child, oldHash, newHash);
    }
}

SingleDrvOutputs DerivationBuilderImpl::registerOutputs(LocalStore & localStore)
{
    std::map<std::string, ValidPathInfo> infos;

    /* Set of inodes seen during calls to canonicalisePathMetaData()
       for this build's outputs.  This needs to be shared between
       outputs to allow hard links between outputs. */
    InodesSeen inodesSeen;

    /* The paths that can be referenced are the input closures, the
       output paths, and any paths that have been built via recursive
       Nix calls. */
    StorePathSet referenceablePaths;
    for (auto & p : inputPaths)
        referenceablePaths.insert(p);
    for (auto & i : scratchOutputs)
        referenceablePaths.insert(i.second);
    for (auto & [p, _] : state_.lock()->addedPaths)
        referenceablePaths.insert(p);

    /* Check whether the output paths were created, and make all
       output paths read-only.  Then get the references of each output (that we
       might need to register), so we can topologically sort them. For the ones
       that are most definitely already installed, we just store their final
       name so we can also use it in rewrites. */
    StringSet outputsToSort;

    struct AlreadyRegistered
    {
        StorePath path;
    };

    struct PerhapsNeedToRegister
    {
        StorePathSet refs;
        /**
         * References to other outputs. Built by looking up in
         * `scratchOutputsInverse`.
         */
        StringSet otherOutputs;
    };

    /* inverse map of scratchOutputs for efficient lookup */
    std::map<StorePath, std::string> scratchOutputsInverse;
    for (auto & [outputName, path] : scratchOutputs)
        scratchOutputsInverse.insert_or_assign(path, outputName);

    std::map<std::string, std::variant<AlreadyRegistered, PerhapsNeedToRegister>> outputReferencesIfUnregistered;
    std::map<std::string, PosixStat> outputStats;
    for (auto & [outputName, _] : drv.outputs) {
        auto scratchOutput = get(scratchOutputs, outputName);
        assert(scratchOutput);
        auto actualPath = realPathInHost(*scratchOutput);

        outputsToSort.insert(outputName);

        /* Updated wanted info to remove the outputs we definitely don't need to register */
        auto initialOutput = get(initialOutputs, outputName);
        assert(initialOutput);
        auto & initialInfo = *initialOutput;

        /* Don't register if already valid, and not checking */
        bool wanted = buildMode == bmCheck || !(initialInfo.known && initialInfo.known->isValid());
        if (!wanted) {
            outputReferencesIfUnregistered.insert_or_assign(
                outputName, AlreadyRegistered{.path = initialInfo.known->path});
            continue;
        }

        auto optSt = maybeLstat(actualPath);
        if (!optSt)
            throw BuildError(
                BuildResult::Failure::OutputRejected,
                "builder for '%s' failed to produce output path for output '%s' at %s",
                store->printStorePath(drvPath),
                outputName,
                PathFmt(actualPath));
        PosixStat & st = *optSt;

#if !defined(__CYGWIN__) && !defined(_WIN32)
        /* Check that the output is not group or world writable, as
           that means that someone else can have interfered with the
           build.  Also, the output should be owned by the build
           user. */
        if ((!S_ISLNK(st.st_mode) && (st.st_mode & (S_IWGRP | S_IWOTH)))
            || (buildUser && st.st_uid != buildUser->getUID()))
            throw BuildError(
                BuildResult::Failure::OutputRejected,
                "suspicious ownership or permission on %s for output '%s'; rejecting this build output",
                PathFmt(actualPath),
                outputName);
#endif

        /* Canonicalise first.  This ensures that the path we're
           rewriting doesn't contain a hard link to /etc/shadow or
           something like that. */
        canonicalisePathMetaData(
            actualPath,
            {
#ifndef _WIN32
                .uidRange = buildUser ? std::optional(buildUser->getUIDRange()) : std::nullopt,
#endif
                NIX_WHEN_SUPPORT_ACLS(localSettings.ignoredAcls)},
            inodesSeen);

        bool discardReferences = false;
        if (auto udr = get(drvOptions.unsafeDiscardReferences, outputName)) {
            discardReferences = *udr;
        }

        StorePathSet references;
        if (discardReferences)
            debug("discarding references of output '%s'", outputName);
        else {
            debug("scanning for references for output '%s' in temp location %s", outputName, PathFmt(actualPath));

            /* Pass blank Sink as we are not ready to hash data at this stage. */
            NullSink blank;
            references = scanForReferences(blank, actualPath, referenceablePaths);
        }

        StringSet referencedOutputs;
        for (auto & r : references)
            if (auto * o = get(scratchOutputsInverse, r))
                referencedOutputs.insert(*o);

        outputReferencesIfUnregistered.insert_or_assign(
            outputName,
            PerhapsNeedToRegister{
                .refs = references,
                .otherOutputs = referencedOutputs,
            });
        outputStats.insert_or_assign(outputName, std::move(st));
    }

    StringSet emptySet;

    auto topoSortResult = topoSort(outputsToSort, [&](const std::string & name) -> const StringSet & {
        auto * orifu = get(outputReferencesIfUnregistered, name);
        if (!orifu)
            throw BuildError(
                BuildResult::Failure::OutputRejected,
                "no output reference for '%s' in build of '%s'",
                name,
                store->printStorePath(drvPath));
        return std::visit(
            overloaded{
                /* Since we'll use the already installed versions of these, we
                   can treat them as leaves and ignore any references they
                   have. */
                [&](const AlreadyRegistered &) -> const StringSet & { return emptySet; },
                [&](const PerhapsNeedToRegister & refs) -> const StringSet & { return refs.otherOutputs; },
            },
            *orifu);
    });

    auto sortedOutputNames = std::visit(
        overloaded{
            [&](Cycle<std::string> & cycle) -> std::vector<std::string> {
                // TODO with more -vvvv also show the temporary paths for manual inspection.
                throw BuildError(
                    BuildResult::Failure::OutputRejected,
                    "cycle detected in build of '%s' in the references of output '%s' from output '%s'",
                    store->printStorePath(drvPath),
                    cycle.path,
                    cycle.parent);
            },
            [](auto & sorted) { return sorted; }},
        topoSortResult);

    OutputPathMap finalOutputs;
    std::vector<PathLocks> dynamicOutputLocks;

    for (auto & outputName : sortedOutputNames | std::views::reverse) {
        auto output = get(drv.outputs, outputName);
        auto scratchPath = get(scratchOutputs, outputName);
        assert(output && scratchPath);
        auto actualPath = realPathInHost(*scratchPath);

        /* An optional file descriptor of a directory used for intermediate
           operations. */
        AutoCloseFD tempDirFd;
        /* RAII cleanup of a temporary directory inside the store that is used
           for intermediate operations. */
        AutoDelete delTempDir;

        auto finish = [&](StorePath finalStorePath) {
            /* Store the final path */
            finalOutputs.insert_or_assign(outputName, finalStorePath);
            /* The rewrite rule will be used in downstream outputs that refer to
               use. This is why the topological sort is essential to do first
               before this for loop. */
            if (*scratchPath != finalStorePath)
                outputRewrites[std::string{scratchPath->hashPart()}] = std::string{finalStorePath.hashPart()};
        };

        auto orifu = get(outputReferencesIfUnregistered, outputName);
        assert(orifu);

        std::optional<StorePathSet> referencesOpt = std::visit(
            overloaded{
                [&](const AlreadyRegistered & skippedFinalPath) -> std::optional<StorePathSet> {
                    finish(skippedFinalPath.path);
                    return std::nullopt;
                },
                [&](const PerhapsNeedToRegister & r) -> std::optional<StorePathSet> { return r.refs; },
            },
            *orifu);

        if (!referencesOpt)
            continue;
        auto references = *referencesOpt;

        auto rewriteOutput = [&](const StringMap & rewrites) {
            /* Apply hash rewriting if necessary. */
            if (!rewrites.empty()) {
                debug("rewriting hashes in %1%; cross fingers", PathFmt(actualPath));

                /* FIXME: Is this actually streaming? */
                auto source = sinkToSource([&](Sink & nextSink) {
                    RewritingSink rsink(rewrites, nextSink);
                    dumpPath(actualPath, rsink);
                    rsink.flush();
                });
                /* Put the temporary copy in a directory inaccessible to the builder.
                   actualPath might point inside the build chroot, which is controlled
                   by the derivation builder. */
                auto [rewriteTempDir, rewriteTempDirFd] = localStore.createTempDirInStore();
                AutoDelete delRewriteTempDir(rewriteTempDir);
                std::filesystem::path tmpPath = rewriteTempDir / "x";
                restorePath(tmpPath, *source);
                deletePath(actualPath);
                movePath(tmpPath, actualPath);

                /* FIXME: set proper permissions in restorePath() so
                   we don't have to do another traversal. */
                canonicalisePathMetaData(
                    actualPath,
                    {
#ifndef _WIN32
                        // builder UIDs are already dealt with
                        .uidRange = std::nullopt,
#endif
                        NIX_WHEN_SUPPORT_ACLS(localSettings.ignoredAcls)},
                    inodesSeen);
            }
        };

        auto rewriteRefs = [&]() -> StoreReferences {
            /* In the CA case, we need the rewritten refs to calculate the
               final path, therefore we look for a *non-rewritten
               self-reference, and use a bool rather try to solve the
               computationally intractable fixed point. */
            StoreReferences res{
                .self = false,
            };
            for (auto & r : references) {
                auto name = r.name();
                auto origHash = std::string{r.hashPart()};
                if (r == *scratchPath) {
                    res.self = true;
                } else if (auto outputRewrite = get(outputRewrites, origHash)) {
                    std::string newRef = *outputRewrite;
                    newRef += '-';
                    newRef += name;
                    res.others.insert(StorePath{newRef});
                } else {
                    res.others.insert(r);
                }
            }
            return res;
        };

        auto newInfoFromCA = [&](const DerivationOutput::CAFloating outputHash) -> ValidPathInfo {
            auto st = get(outputStats, outputName);
            if (!st)
                throw BuildError(
                    BuildResult::Failure::OutputRejected,
                    "output path %1% without valid stats info",
                    PathFmt(actualPath));
            if (outputHash.method.getFileIngestionMethod() == FileIngestionMethod::Flat) {
                /* The output path should be a regular file without execute permission. */
                if (!S_ISREG(st->st_mode) || (st->st_mode & S_IXUSR) != 0)
                    throw BuildError(
                        BuildResult::Failure::OutputRejected,
                        "output path %1% should be a non-executable regular file "
                        "since recursive hashing is not enabled (one of outputHashMode={flat,text} is true)",
                        PathFmt(actualPath));
            }
            rewriteOutput(outputRewrites);
            /* FIXME optimize and deduplicate with addToStore */
            std::string oldHashPart{scratchPath->hashPart()};
            auto got = [&] {
                auto fim = outputHash.method.getFileIngestionMethod();
                switch (fim) {
                case FileIngestionMethod::Flat:
                case FileIngestionMethod::NixArchive: {
                    MaskedHashSink caSink{outputHash.hashAlgo, oldHashPart};
                    auto fim = outputHash.method.getFileIngestionMethod();
                    dumpPath(
                        {makeFSSourceAccessor(actualPath), CanonPath::root}, caSink, (FileSerialisationMethod) fim);
                    return caSink.finish().hash;
                }
                case FileIngestionMethod::Git: {
                    return git::dumpHash(outputHash.hashAlgo, {makeFSSourceAccessor(actualPath), CanonPath::root}).hash;
                }
                }
                assert(false);
            }();

            auto newInfo0 = ValidPathInfo::makeFromCA(
                *store,
                outputPathName(drv.name, outputName),
                ContentAddressWithReferences::fromParts(outputHash.method, std::move(got), rewriteRefs()),
                Hash::dummy);
            if (*scratchPath != newInfo0.path) {
                // If the path has some self-references, we need to rewrite
                // them.
                // (note that this doesn't invalidate the ca hash we calculated
                // above because it's computed *with the self-references masked*, so
                // it already takes this rewrite into account).
                rewriteOutput(StringMap{{oldHashPart, std::string(newInfo0.path.hashPart())}});
            }

            {
                HashResult narHashAndSize = hashPath(
                    {makeFSSourceAccessor(actualPath), CanonPath::root},
                    FileSerialisationMethod::NixArchive,
                    HashAlgorithm::SHA256);
                newInfo0.narHash = narHashAndSize.hash;
                newInfo0.narSize = narHashAndSize.numBytesDigested;
            }

            assert(newInfo0.ca);
            return newInfo0;
        };

        auto moveOutputToTempDir = [&]() -> void {
            std::filesystem::path tempDir;
            std::tie(tempDir, tempDirFd) = localStore.createTempDirInStore();
            delTempDir = AutoDelete(tempDir);

            auto tmpOutput = tempDir / "x";

            /* Copy files to break stale file descriptors. copyRecursive below will use
               reflinking to optimise the copying overhead. */
            auto pathAccessor = makeFSSourceAccessor(actualPath);
            RestoreSink restoreSink{store->getLocalSettings().fsyncStorePaths};
            restoreSink.dstPath = tmpOutput;
            copyRecursive(*pathAccessor, CanonPath::root, restoreSink, CanonPath::root);
            /* This makes it slightly harder to make sense of the control flow. The rule
               of thumb is that actualPath points to the current location of the stuff
               that we'll end up registering. */
            actualPath = std::move(tmpOutput);
        };

        ValidPathInfo newInfo = std::visit(
            overloaded{

                [&](const DerivationOutput::InputAddressed & output) {
                    /* CASPER: Content-Addressable Store via Partial-blinding and Embedded Relocation */
                    std::optional<std::pair<uid_t, gid_t>> builderOwner;
#ifndef _WIN32
                    if (buildUser)
                        builderOwner = std::make_pair(buildUser->getUID(), buildUser->getGID());
#endif
                    auto rootSt = lstat(actualPath);
                    bool hasCustomRelocate = false;
                    if (S_ISDIR(rootSt.st_mode)) {
                        chmod(actualPath, (rootSt.st_mode & ~S_IFMT) | S_IWUSR);
                        auto nixSupportDir = actualPath / "nix-support";
                        auto optSupportSt = maybeLstat(nixSupportDir);
                        if (!optSupportSt || S_ISDIR(optSupportSt->st_mode)) {
                            createDirs(nixSupportDir);
                            chmod(nixSupportDir, 0755);
                            auto relocateScript = nixSupportDir / "relocate.sh";
                            if (pathExists(relocateScript)) {
                                hasCustomRelocate = true;
                            } else {
                                writeFile(relocateScript, defaultRelocateScript, 0755);
                                chmod(relocateScript, 0755);
                            }
                            auto hashScript = nixSupportDir / "hash.sh";
                            if (!pathExists(hashScript)) {
                                writeFile(hashScript, defaultHashScript, 0755);
                                chmod(hashScript, 0755);
                            }
                        }
                    }

                    bool needRelocateScript = hasCustomRelocate || hasGzFiles(actualPath);

                    /* Rewrite any earlier outputs of this derivation first */
                    for (auto & [oldDepHash, newDepHash] : outputRewrites) {
                        if (needRelocateScript) {
                            preparePathForRelocation(actualPath, builderOwner);
                            runRelocateScript(*scratchPath, oldDepHash, newDepHash);
                        }
                        rewritePathInPlace(actualPath, oldDepHash, newDepHash);
                    }

                    /* Step 1: Blind self-references from <scratchHash>-<name> to xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx-<name> */
                    std::string outBaseName{output.path.name()};
                    std::string oldSelf{scratchPath->to_string()};
                    std::string blindSelf = std::string(StorePath::HashLen, 'x') + "-" + outBaseName;
                    if (needRelocateScript) {
                        preparePathForRelocation(actualPath, builderOwner);
                        runRelocateScript(*scratchPath, oldSelf, blindSelf);
                    }
                    rewritePathInPlace(actualPath, oldSelf, blindSelf);

                    /* Step 2: Hash the blinded output and compute content-addressed store path */
                    HashResult normalizedNar = hashPath(
                        {makeFSSourceAccessor(actualPath), CanonPath::root},
                        FileSerialisationMethod::NixArchive,
                        HashAlgorithm::SHA256);
                    StorePath caOutPath = store->makeContentAddressedOutputPath(
                        normalizedNar.hash, outBaseName);
                    std::string newSelf{caOutPath.to_string()};

                    /* Step 3: Relocate self-references from xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx-<name> to <outHash>-<name> */
                    if (needRelocateScript) {
                        preparePathForRelocation(actualPath, builderOwner);
                        runRelocateScript(*scratchPath, blindSelf, newSelf);
                    }
                    rewritePathInPlace(actualPath, blindSelf, newSelf);

                    /* Step 4: Canonicalize metadata and compute final NAR hash */
                    canonicalisePathMetaData(
                        actualPath,
                        {
#ifndef _WIN32
                            .uidRange = std::nullopt,
#endif
                            NIX_WHEN_SUPPORT_ACLS(localSettings.ignoredAcls)},
                        inodesSeen);

                    HashResult narHashAndSize = hashPath(
                        {makeFSSourceAccessor(actualPath), CanonPath::root},
                        FileSerialisationMethod::NixArchive,
                        HashAlgorithm::SHA256);
                    ValidPathInfo newInfo0{caOutPath, {*store, narHashAndSize.hash}};
                    newInfo0.narSize = narHashAndSize.numBytesDigested;

                    bool discardReferences = false;
                    if (auto udr = get(drvOptions.unsafeDiscardReferences, outputName))
                        discardReferences = *udr;

                    auto refs = rewriteRefs();
                    newInfo0.references = std::move(refs.others);
                    if (!discardReferences && (refs.self || narHashAndSize.hash != normalizedNar.hash))
                        newInfo0.references.insert(newInfo0.path);
                    return newInfo0;
                },

                [&](const DerivationOutput::CAFixed & dof) {
                    auto & wanted = dof.ca.hash;
                    moveOutputToTempDir();
                    return newInfoFromCA(
                        DerivationOutput::CAFloating{
                            .method = dof.ca.method,
                            .hashAlgo = wanted.algo,
                        });
                },

                [&](const DerivationOutput::CAFloating & dof) { return newInfoFromCA(dof); },

                [&](const DerivationOutput::Deferred &) -> ValidPathInfo {
                    // No derivation should reach that point without having been
                    // rewritten first
                    assert(false);
                },

                [&](const DerivationOutput::Impure & doi) {
                    moveOutputToTempDir();
                    return newInfoFromCA(
                        DerivationOutput::CAFloating{
                            .method = doi.method,
                            .hashAlgo = doi.hashAlgo,
                        });
                },

            },
            output->raw);

        /* FIXME: set proper permissions in restorePath() so
            we don't have to do another traversal. */
        canonicalisePathMetaData(
            actualPath,
            {
#ifndef _WIN32
                // builder UIDs are already dealt with
                .uidRange = std::nullopt,
#endif
                NIX_WHEN_SUPPORT_ACLS(localSettings.ignoredAcls)},
            inodesSeen);

        /* Calculate where we'll move the output files. In the checking case we
           will leave leave them where they are, for now, rather than move to
           their usual "final destination" */
        auto finalDestPath = store->printStorePath(newInfo.path);

        /* Lock final output path, if not already locked. This happens with
           floating CA derivations, CASPER-relocated input-addressed derivations,
           and hash-mismatching fixed-output derivations. */
        auto & dynamicOutputLock = dynamicOutputLocks.emplace_back();
        dynamicOutputLock.setDeletion(true);
        auto optFixedPath = output->path(*store, drv.name, outputName);
        if (!optFixedPath || store->printStorePath(*optFixedPath) != finalDestPath) {
            bool isInputAddressed = std::holds_alternative<DerivationOutput::InputAddressed>(output->raw);
            bool isCAFixed = std::holds_alternative<DerivationOutput::CAFixed>(output->raw);
            assert(newInfo.ca || isInputAddressed);

            /* Don't wait on lock for the hash-mismatching fixed-output
               derivation case, to avoid a deadlock in the case where a build
               with the correct hash is in progress. */
            bool locked = dynamicOutputLock.lockPaths({store->toRealPath(newInfo.path)}, "", !isCAFixed);

            /* If we can't lock the correct path, clean up and bail now. */
            if (!locked) {
                debug(
                    "failed to lock correct output path of %s, namely %s, not moving output",
                    store->printStorePath(drvPath),
                    PathFmt(store->toRealPath(newInfo.path)));
                deletePath(actualPath);
                /* Trigger the hash-mismatch error. */
                checkCAOutput(*store, drvPath, *output, newInfo, outputName);
                unreachable();
            }
        }

        /* Move files, if needed */
        if (store->toRealPath(newInfo.path) != actualPath) {
            if (buildMode == bmRepair) {
                /* Path already exists, need to replace it */
                replaceValidPath(store->toRealPath(newInfo.path), actualPath);
            } else if (buildMode == bmCheck) {
                /* Path already exists, and we want to compare, so we leave out
                   new path in place. */
            } else if (localStore.isValidPath(newInfo.path)) {
                /* Path already exists because CA path produced by something
                   else. No moving needed. */
                assert(newInfo.ca || std::holds_alternative<DerivationOutput::InputAddressed>(output->raw));
                /* Can delete our scratch copy now. */
                deletePath(actualPath);
            } else {
                auto destPath = store->toRealPath(newInfo.path);
                deletePath(destPath);
                movePath(actualPath, destPath);
            }
        }

        if (buildMode == bmCheck) {
            /* Check against already registered outputs */
            StorePath oldPath = newInfo.path;
            if (auto * ia = std::get_if<DerivationOutput::InputAddressed>(&output->raw)) {
                oldPath = localStore.resolveInputPath(ia->path);
            }

            if (localStore.isValidPath(oldPath)) {
                ValidPathInfo oldInfo(*localStore.queryPathInfo(oldPath));
                if (newInfo.path != oldInfo.path || newInfo.narHash != oldInfo.narHash) {
                    auto * diffHook = localSettings.getDiffHook();
                    if (diffHook || settings.keepFailed) {
                        auto dst = store->toRealPath(oldInfo.path);
                        dst += ".check";
                        deletePath(dst);
                        movePath(actualPath, dst);

                        if (diffHook) {
                            handleDiffHook(
                                *diffHook,
#ifndef _WIN32
                                buildUser ? buildUser->getUID() : getuid(),
                                buildUser ? buildUser->getGID() : getgid(),
#endif
                                store->printStorePath(oldInfo.path),
                                dst,
                                store->printStorePath(drvPath),
                                tmpDir);
                        }

                        throw NotDeterministic(
                            "derivation '%s' may not be deterministic: output %s differs from %s",
                            store->printStorePath(drvPath),
                            PathFmt(store->toRealPath(oldInfo.path)),
                            PathFmt(dst));
                    } else
                        throw NotDeterministic(
                            "derivation '%s' may not be deterministic: output %s differs",
                            store->printStorePath(drvPath),
                            PathFmt(store->toRealPath(oldInfo.path)));
                }

                /* Since we verified the build, it's now ultimately trusted. */
                if (!oldInfo.ultimate) {
                    oldInfo.ultimate = true;
                    localStore.signPathInfo(oldInfo);
                    localStore.registerValidPaths({{oldInfo.path, oldInfo}});
                }
            }
        } else {
            /* do tasks relating to registering these outputs */

            /* For debugging, print out the referenced and unreferenced paths. */
            for (auto & i : inputPaths) {
                if (references.count(i))
                    debug("referenced input: '%1%'", store->printStorePath(i));
                else
                    debug("unreferenced input: '%1%'", store->printStorePath(i));
            }

            if (!localStore.isValidPath(newInfo.path))
                localStore.optimisePath(
                    store->toRealPath(newInfo.path), NoRepair); // FIXME: combine with scanForReferences()

            newInfo.deriver = drvPath;
            newInfo.ultimate = true;
            localStore.signPathInfo(newInfo);

            finish(newInfo.path);

            /* If it's a CA path, register it right away. This is necessary if it
               isn't statically known so that we can safely unlock the path before
               the next iteration

               This is also good so that if a fixed-output produces the
               wrong path, we still store the result (just don't consider
               the derivation successful, so if someone fixes the problem by
               just changing the wanted hash, the redownload (or whateer
               possibly quite slow thing it was) doesn't have to be done
               again. */
            if (newInfo.ca)
                localStore.registerValidPaths({{newInfo.path, newInfo}});
        }

        /* Do this in both the check and non-check cases, because we
           want `checkOutputs` below to work, which needs these path
           infos. */
        infos.emplace(outputName, std::move(newInfo));
    }

    /* Apply output checks. This includes checking of the wanted vs got
       hash of fixed-outputs. */
    checkOutputs(localStore, drvPath, drv, drvOptions.outputChecks, infos);

    if (buildMode == bmCheck) {
        return {};
    }

    /* Register each output path as valid, and register the sets of
       paths referenced by each of them.  If there are cycles in the
       outputs, this will fail. */
    {
        ValidPathInfos infos2;
        for (auto & [outputName, newInfo] : infos) {
            infos2.insert_or_assign(newInfo.path, newInfo);
        }
        localStore.registerValidPaths(infos2);
        for (auto & [outputName, newInfo] : infos) {
            if (auto output = get(drv.outputs, outputName)) {
                if (auto * ia = std::get_if<DerivationOutput::InputAddressed>(&output->raw)) {
                    localStore.addPathRewrite(ia->path, newInfo.path, drvPath, outputName);
                }
            }
        }
    }

    /* If we made it this far, we are sure the output matches the
       derivation That means it's safe to link the derivation to the
       output hash. We must do that for floating CA derivations, which
       otherwise couldn't be cached, but it's fine to do in all cases.
       */
    SingleDrvOutputs builtOutputs;

    for (auto & [outputName, newInfo] : infos) {
        auto oldinfo = get(initialOutputs, outputName);
        assert(oldinfo);
        auto thisRealisation = Realisation{
            {
                .outPath = newInfo.path,
            },
            DrvOutput{
                .drvPath = drvPath,
                .outputName = outputName,
            },
        };
        if (experimentalFeatureSettings.isEnabled(Xp::CaDerivations) && !type(drv).isImpure()) {
            localStore.signRealisation(thisRealisation);
            localStore.registerDrvOutput(thisRealisation, NoCheckSigs);
        }
        builtOutputs.emplace(outputName, thisRealisation);
    }

    return builtOutputs;
}

SingleDrvOutputs DerivationBuilderImpl::checkSubmittedOutputs(LocalStore & localStore)
{
    // Submitted outputs from the recursive nix daemon
    // It's fine to lock here since all other threads with the reference have been shut down.
    auto submittedOutputs(this->submittedOutputs.lock());

    SingleDrvOutputs builtOutputs;

    std::map<std::string, ValidPathInfo> infos;

    for (auto & [outputName, outputPath] : *submittedOutputs) {
        infos.emplace(outputName, *localStore.queryPathInfo(outputPath));
    }

    // checkOutputs only performs checks that make sense for both submitting and non-submitting derivations,
    // more verification steps needed afterward
    checkOutputs(localStore, drvPath, drv, drvOptions.outputChecks, infos);

    for (auto & [outputName, output] : drv.outputs) {
        // For some reason cannot be moved to checkOutputs, needs debugging
        if (!submittedOutputs->contains(outputName)) {
            throw BuildError(
                BuildResult::Failure::OutputRejected,
                "builder for '%s' failed to submit output path for '%s'",
                store->printStorePath(drvPath),
                outputName);
        }

        // We should have already checked that the derivation is content-addressing in startBuild
        // and that the outputs of a content-addressing derivation is content-addressed in checkOutputs.
        // Add an assert here just in case, but it should never trigger.
        assert(
            std::get_if<DerivationOutput::CAFloating>(&output.raw)
            || std::get_if<DerivationOutput::CAFixed>(&output.raw));

        // No need to sign CA outputs, only the realisation matters
        auto realisation = Realisation{
            {
                .outPath = *get(*submittedOutputs, outputName),
            },
            DrvOutput{
                .drvPath = drvPath,
                .outputName = outputName,
            },
        };

        localStore.signRealisation(realisation);
        localStore.registerDrvOutput(realisation, NoCheckSigs);
        builtOutputs.emplace(outputName, realisation);

        // TODO: handle --check
    }

    return builtOutputs;
}

BuildingStore::~BuildingStore() = default;

namespace {

struct LocalBuildingStore : BuildingStore
{
    LocalStore & localStore;

    LocalBuildingStore(LocalStore & localStore)
        : BuildingStore{localStore.storeDir}
        , localStore{localStore}
    {
    }

    std::filesystem::path getRealStoreDir() const override
    {
        return localStore.config->realStoreDir.get();
    }

    std::filesystem::path getBuildDir() const override
    {
        return localStore.config->getBuildDir();
    }

    const LocalSettings & getLocalSettings() const override
    {
        return localStore.config->getLocalSettings();
    }

    ref<Store> makeRecursiveNixStore(RestrictionContext & ctx) override
    {
        return makeRestrictedStore(
            [&] {
                auto config = make_ref<LocalStore::Config>(*localStore.config);
                config->pathInfoCacheSize = 0;
                config->stateDir = "/no-such-path";
                config->logDir = "/no-such-path";
                return config;
            }(),
            ref<LocalStore>(std::dynamic_pointer_cast<LocalStore>(localStore.shared_from_this())),
            ctx);
    }
};

} // namespace

std::unique_ptr<BuildingStore> makeBuildingStoreFromLocalStore(LocalStore & localStore)
{
    return std::make_unique<LocalBuildingStore>(localStore);
}

} // namespace nix
