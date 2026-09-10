# Independent setup review

Reviewed `docs/PLAN.md`, `tools/{lake,images,upstream,inventory}.py`, `Audit.lean`, `Xv6/Image/Hex.lean`, `Xv6/Images.lean`, generated images' structure, tests, pins and root import graph. This review does not certify the full port; no whole-system theorem exists yet.

## Findings to resolve before reporting the setup complete

### 1. Preserve the xv6 software license with imported binaries

The exact pinned source https://github.com/mit-pdos/xv6-riscv/blob/45071c74c56b216a76bc08213d6c7a90b8f0688b/LICENSE has the MIT license. Its copyright holders are Frans Kaashoek, Robert Morris, Russ Cox and Massachusetts Institute of Technology, years 2006–2024. It requires retaining the copyright and permission notice with copies/substantial portions. Kernel ELF and fs.img contain copies of this software; keep the full original license, e.g. `LICENSES/xv6-riscv.txt`, and reference it from the image provenance documentation. Raw URL for the exact notice: https://raw.githubusercontent.com/mit-pdos/xv6-riscv/45071c74c56b216a76bc08213d6c7a90b8f0688b/LICENSE . This is separate from the absence of a license in the xv6iris proof repository. No need to invent a license for xv6iris.

### 2. Default build/audit currently omits the memory port

At review time `MachCSL.lean` imports only `MachCSL.Logic`. `MachCSL/Memory/Defs.lean` and `Proofs.lean` therefore are not in the imported environment audited by `Audit.lean` and are not reached by the default root import build. The memory worker may still be finishing, but root must import those finished modules and run the build/audit before counting them as integrated.

The audit comment's claim to audit all project declarations is also too broad: it visits only the imported environment and only names with `MachCSL.`/`Xv6.` prefixes. Private declaration names start with `_private.` and are skipped, though any private dependency actually used by an audited public declaration still has its axioms checked transitively. Recommended: enforce a manifest/import-coverage check for project modules and select project declarations by defining module (including private names), or explicitly document the narrower checked scope. A missing private axiom which is not used cannot compromise checked public theorems but contradicts an 'all declarations/no project axioms' policy.

## Smaller reproducibility and robustness findings

- `tools/lake.py` successfully avoids source edits in dependency packages and uses Lean's explicit `-j2`, which is needed on this 144-core host. However its common `.cache/lean-limited` sysroot is updated by unlinking/relinking symlinks on every invocation. Concurrent invocations can transiently break another build's search paths; writing the shell wrapper nonatomically also races. A version/thread-specific immutable sysroot assembled in a temporary directory, or a lock around creation with no rewrites if already correct, avoids this. This is particularly relevant to a multi-agent repository.
- The wrapper resolves whichever `lean` and `lake` are found on PATH. CWD selects the pin only if these are elan shims. Its error message tells users to put elan on PATH, but no version equality is checked. Validate selected compiler version/commit against the toolchain pin, especially when LEAN_SYSROOT/ELAN_TOOLCHAIN is inherited or users have a direct Lean binary first on PATH.
- Root `weakLeanArgs=["-j2"]` is now redundant with the wrapper and overrides `XV6_LEAN_THREADS=1` for root modules because later Lean arguments win. Either document the hard root limit or remove the root override once the wrapper is the build entry point.
- `tools/inventory.py` uses `source.rglob('*.v')` rather than `git ls-files`. Ignored generated `.v` files can enter the supposedly pinned inventory despite clean `git status`. Enumerate tracked files to make the index exactly a function of the pinned Git revision. Current pristine checkout inventory remains usable.
- `tools/images.extract` is a regex extractor, not a fully fail-closed parser: an invalid extra chunk definition, e.g. a chunk containing `zz`, is silently skipped if earlier valid chunks match. The main command's fixed size and SHA256 checks protect the concrete images from this weakness; there is no demonstrated wrong-byte acceptance in main. Clarify the helper/test label or separately reject any chunk-like declaration that fails syntax validation, and test malformed chunk cases.
- `tools/upstream.py` leaves an initialized directory after failed network fetch. A rerun sees an existing directory and errors on missing HEAD rather than finishing/retrying. Fetch into a temporary directory and rename after success, or handle an empty initialized repo explicitly. Existing successful pristine checkouts are checked correctly and never silently moved.

## Positive checks

- The plan is explicit that the full project is incomplete and preserves the paper's essential concurrency, crash and TSO limits. Its first closed slice is correctly identified as a gate, not completion. The planned real Iris model and initialized adequacy avoid a Prop/WP surrogate.
- Image hashes, sizes and exact source revision are independently checked by the generator. `--check` compares the complete generated text. The root image representation is compact hex rather than millions of elaborated byte constructors.
- The Lean hex decoder accepts ASCII hex only, rejects uneven chunks and preserves byte order. UInt8 arithmetic cannot overflow for actual nibble values beyond the intended byte because each accepted nibble is at most 15. Its concrete examples use kernel `decide`, not `native_decide` proof axioms.
- Image runtime tests distinguish executable checks from proofs of ELF/filesystem validity; `Option ByteArray` makes malformed input explicit. Both full images are checked for expected decoded sizes and the kernel for ELF magic. No theorem falsely claims fs.img consistency or ELF loading correctness.
- Axiom auditing calls Lean's transitive `collectAxioms`; it fails for unapproved axioms and an empty theorem population. Explicit checks of upstream generic adequacy and fancy-update soundness are appropriate. The imported public theorem closure is meaningfully checked despite the scope limitation described above.
- Ran `python3 -m unittest discover -s tests -v`: all four existing importer tests passed. Did not interfere with root's in-progress full build.

## Recommended immediate disposition

Retain exact xv6 license; integrate memory imports once worker completes; tighten audit scope/import coverage; stabilize the shared build-wrapper sysroot for concurrent agents. Remaining importer/checkout robustness improvements are bounded follow-ups and do not demonstrate incorrect current generated data. Refresh STATUS after completed checks: its Iris integration and transitive-checking entries were stale at review time.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
