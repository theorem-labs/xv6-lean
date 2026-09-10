# xv6iris paper artifact audit

Audited after reading all 47 pages of arXiv:2609.04043v1. No upstream build has been independently replayed in this audit; source-level inventory and decoded image hashes are verified locally. No outward posts were made.

## Immutable baseline

Use the authors' annotated `arxiv-v1` tag, whose message is “snapshot as of arxiv tech report v1”. Tag object `fc9a61fce7ae428e303b8c165e304e26700d816c`; target commit `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The tag contains an SSH signature, which this audit has not verified. Read-only checkout: `/tmp/xv6-lean-research/xv6iris-arxiv-v1`.

The separately cloned HEAD `/tmp/xv6-lean-research/xv6iris` is `7d346ab77849995c963cd99f26311f5a845c5b42` (September 10). HEAD is **not** the paper model: it has relaxed load-load ordering, a noncoherent instruction view, a newer Sail pin, and a PID wraparound kernel fix. Do not port HEAD while calling the result paper-faithful without an explicit scope change.

At the paper tag:

- xv6: `https://github.com/mit-pdos/xv6-riscv`, `45071c74c56b216a76bc08213d6c7a90b8f0688b`; source tree is ignored and fetched separately by the Makefile. `verified` is rebased, so immutable hashes matter.
- Sail RISC-V: `https://github.com/zeldovich/sail-riscv`, `23dcf8fd923eb8a1958795393d2975632aa940b2`. Fork includes atomic PTE A/D updates and Rocq platform-hook bindings. The generated Rocq semantics are tracked.
- `.github/coq-deps.txt`: coq 9.0.1, coq-iris 4.4.0, coq-stdpp 1.12.0, coq-stdpp-bitvector 1.12.0, coq-sail-stdpp 0.20.1. CI uses OCaml 5.3. Sail compiler version is not pinned reproducibly: regeneration reads its installed version and can lower `--require-version` to that version.
- Config: `model-xv6iris/sail-config-rv64d.json`; module list `model-xv6iris/sail-modules.txt`; hand-written hooks `model-xv6iris/xv6iris_extras.v`. The JSON header has historical wording; inspect values/model gating rather than infer all enabled extensions from its name.
- `Arch.pa` is a 64-bit word at `model-xv6iris/rv64d_types.v:14781`, while hardware `physaddr_bits` is 56. The port must distinguish the carrier from physical-address validity.

No AGENTS.md exists in upstream. Root CLAUDE.md points to `claude-notes/README.md` and `durable-notes.md`; both were read. No LICENSE or COPYING file exists in the tag or cloned HEAD, and the inspected generated model/tool headers carry no license grant. Preserve this provenance gap explicitly; do not silently label upstream material MIT. Dependencies' separate notices do not establish a license for this artifact.

## Exact target and assumptions

The concrete theorem is `iris/SystemAdequacy.v:1190`, `xv6_fs_adequacy_xv6Σ`:

Given initial `ggen = 0`, `gpow = false`, and durable disk equal to the literal `FsImgDisk.fsimg_dk`, every state `(t2,g2)` reachable by `rtc erased_step` from `([PowerLoopE],g)` has every thread reducible and satisfies `xv6_trace_pure fsimg_cov (sb_logstart fsimg_sb) g2`.

`xv6_trace_pure` (`SystemAdequacy.v:245`) conjoins `fs_boot_pure` of the durable disk with `gpow = true → resv_ok g`. `fs_boot_pure` (`:149`) states extent geometry, existence of a recovered committed block map D, well-formed log header, and existence of abstract FS state S with `FsDurSnap.snap_ok S D`. `snap_ok` (`FsDurSnap.v:521`) is byte-encoding validity plus per-inode local invariants; its dependency closure includes block/bitmap disjointness and link-resource validity. It is not an arbitrary “OS functional correctness” or noninterference claim.

The hardware transition itself reloads the fixed kernel image at each power-on. `RiscvLang.v:1379` defines `boot_shape` using `virtio_reset g.gdev.dvirtio`, preserving the *current durable disk*. PowerOff increments generation and disables old threads; PowerOn starts eight harts plus UART, disk and PLIC loops. No premise restores fs.img after each crash.

Other roots: generic `RiscvAdequacy.riscv_power_adequacy`; `SystemAdequacy.xv6_power_adequacy_xv6Σ` has a client-supplied invariant-extraction hypothesis; `xv6_trace_adequacy_xv6Σ` has client trace-resource obligations; `xv6_obs_wf_xv6Σ` is a concrete observable-trace well-formedness corollary. Preserve that distinction.

`iris/SystemAssumptions.v` audits only the concrete FS theorem and documents exactly thirteen expected assumptions: dependent functional extensionality, `xv6iris_extras.resv_matches`, `xv6iris_extras.resv_is_valid`, and ten Rocq PrimString/PrimInt63 primitives (`string/get/cat`, `int/eqb/sub/lsl/lsr/land/lor`). The two reservation predicates are arbitrary fixed functions/Boolean; effectful load/cancel hooks are no-ops in modeled state. Instantiating them to false would weaken the platform class. In Lean prefer explicit universally quantified platform parameters rather than untracked axioms.

The expected assumption baseline is source documentation, not a freshly replayed `Print Assumptions` result. This machine has opam switches but the checked rocq-9.0 switch lacks Iris/Sail dependencies. A Lean `#print axioms` gate must eventually target closed concrete theorem roots, not merely generic conditional wrappers.

Safety does not imply liveness, termination, no deadlocks, secrecy or noninterference. Resource-exhaustion `panic` prints/spins and is proven safe; `unreachable` deliberately has no function spec. TSO is not full RVWMO. Paper Sail TLB is 64-entry direct mapped. Device conformance is testing, not a proof that real hardware refines the model.

## Binary provenance

Decoded tracked hex literals independently, without building or mutating upstream. These are the exact bytes to pin:

| Input | Bytes | SHA256 |
|---|---:|---|
| KernelElfRaw.v | 285560 | b4bd19f162efb9584b841508408035de7e41a4c680311a514e4e78b8f06eedd8 |
| FsImgRaw.v | 2048000 | 77f42e2f20c0c2c72234dc9ea034f808a26a003f50e7bba62befe8c174bd07b5 |
| InitElfRaw.v | 35976 | b2c05b19834e4f72a3f45470e469ac709118bdff7e0adb15d07b0ac94c635aac |
| ShElfRaw.v | 58312 | 02b582177e64fc262a37350980a0801ece72dc4d9bcfa77c7692888e8dbb025e |
| EchoElfRaw.v | 35592 | 31831c6c6681c276a121cca1fda3d85535f5f6d7dfbc3ac1790f76a4b0fa7db3 |
| SyncElfRaw.v | 34944 | 444ac218c1aa3c8842a44499b224e010685d9bb9dde9f7f059943a6fbbc2b0b7 |

Generated model `rv64d_types.v` SHA256 e80574854f2831805b275e543182482afb02488e7cdc2a145b651d6b58353ebf; `rv64d.v` f6f2234b9229f7b834e7ae4a5494ace24afac1f286eecc8847144fd5b4d01f28; config 3ab738f89ebe791a13195f00c04b2682bf7c9226e638e58c5eed8b207b6a3f6e; modules 751dab3aabdfbfa544a87d9cc7f02044cfc17225943cb5a28366db7688dc6b54.

`tools/dump_elf.py` already has Lean output modes, but its derived decoded facts must still be kernel checked. Tracked raw literals are the primary concrete inputs. `iris/ElfFile.v`, `ElfKernel.v`, `FsImg.v`, `FsImgCheck.v`, and `FsImgDisk.v` connect raw bytes to loader state and initial FS invariants. Upstream docs contain stale binary sizes and code counts; use actual constants.

## Inventory and dependency DAG

Paper checkout counts (physical .v files / lines): iris 1498 / 1093172; model 4 / 60020; kernel data 5 / 60218; user data 19 / 33844; conformance 290 / 78659. Iris `_CoqProject` activates 1427 files and explicitly parks 71. Parked files include stronger AU syscall contracts, name traversal variants and user shell work; “port all supporting proofs for the paper theorem” and “port every experimental file in the repository” differ.

Static `tools/proof_coverage.py` reports 189/190 kernel functions proven, 23728/23746 text bytes, 0 assumed, 0 partial. The sole uncovered symbol is `unreachable` (18 bytes). Source attribution is absent because the separate xv6 checkout was not present. The report is `/tmp/xv6-lean-research/paper-coverage.md`; it is a static report, not proof checking.

Comment-stripped syntactic import analysis: SystemAdequacy's file cone has 1312 local files, including 1290 iris files; no parked file occurs in the cone. There are no `Axiom` or `Admitted` declarations in iris after removing comments; 331 `Parameter` keywords are largely module-type contracts, not global logical assumptions. Two `Abort` commands occur outside that cone. Exact external library dependencies and proof-term dependencies require Rocq tooling; this import graph is only a planning graph. Saved as `paper-import-graph.json` and `paper-system-cone.txt` beside this report.

Port dependency order:

1. Finite maps, bitvectors/byte serialization, Iris OFEs/CMRAs/uPred/BI/fancy updates/invariants/WP adequacy. Audit existing iris-lean before choosing reuse versus extension.
2. Sail deep event monad and generated RISC-V semantics at the paper pin/config, platform hooks; production memory model `TsoMemPa.v`, device models `VirtioModel.v`/`DevModel.v`, exact subinstruction `RiscvLang.v`, power/reset model. `TsoMem.v` is the dependency-light litmus model; it is NOT directly imported by RiscvLang. Do not replace event-level monadic continuations with a state executor that hides interleavings.
3. `RiscvPtsto.v`, `TsoGhost.v`, `TsoCtx.v`, ghost transport, `Hart*.v` liftings, `RiscvExec.v`, reset proofs and abstract machine adequacy. Keep register resources indexed by hart and generation.
4. Instruction fetch/decode/execute, page-table/TLB proofs, translation tiers, interrupts, context migration, stack budgets/reclaim. Agree on invariants before fanning out proofs.
5. Per-function Spec/Code/Proof/Link families: memory and boot; spinlocks/sleeplocks; scheduler/procs/user-mode isolation; devices; buffer cache; WAL; inode/link/file tree; descriptors/pipes/syscalls. Some module-contract dependencies are mutually recursive at the specification level, so retain sealed interfaces and late linking.
6. Raw kernel/fs byte import and checked decoding/ELF/FS initial-state certificates can run in parallel with 2–5. Close concrete SystemAdequacy theorem only after linking every contract and discharging image/boot obligations. Audit axioms and model definition dependency cone; test conformance and negative/vacuity cases.

Prioritized first slice: production TSO core and properties, pinned byte provenance and parser validation, and a genuine Sail event interface. Then one nontrivial instruction through a linked machine safety proof; only after contract review allocate kernel proof batches.

Agent management from paper §7: coordinator owns abstractions/specs; workers own bounded proof files; review difficult concurrency designs against code before scaling; checkpoint precise unmet obligations; discard failed abstractions rather than endlessly append helper lemmas. Keep proof checking fast, contracts stable, commits attributable, and completion claims tied to closed theorem roots.

*Authorship note: this was researched and written by an AI coding agent (OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is posted from this account.*

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
