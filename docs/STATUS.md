# Project status

The full Lean port is **not complete**. No Lean theorem currently establishes xv6
whole-system safety or filesystem crash consistency.

| Workstream | Status | Current owner / next gate |
|---|---|---|
| Full paper reading | Complete (47 pages) | Codex coordinator and audit agents |
| Baseline audit | Paper tag identified | Exact pins and image hashes recorded |
| Independent design reviews | Initial plan and revised plan complete; focused JAL and two-hart design reviews also complete | Claude Code, Fable 5.1, max effort; see reviews/fable-disposition.md and reviews/fable-jal-loop.md and reviews/fable-two-hart-disposition.md |
| Reproducible repository/tooling | Implemented; initial GitHub CI passed | Build, imports, image decoding and source regeneration pass |
| Native Iris build and integration | Complete initial integration | Generic adequacy axiom audit passed |
| Production TSO memory port | Core, byte read/write and finite-map/reservation bridges proved | See MachCSL/Memory/STATUS.md for missing layers |
| Sail free V1 event interface | Implemented and independently reviewed | Absent-write payload behavior corrected from pinned Rocq source |
| Generic event execution and result transport | Proved initial composition/inversion laws | Actual handlers, blocked steps and restart rules implemented; correspondence pending |
| Full generated Lean RISC-V model | Compiled; six execution/reset entry cones audited; real fetched JAL execution proved | Two explicit reservation predicates; full semantic correspondence pending |
| Machine/device/power language | Concrete language implemented, including Virtio DMA and power | Boot execution and arbitrary-schedule memory/reservation/trace invariants proved; ownership in progress |
| TSO ownership | Native byte/timestamp, log, view, dirty-set and full heap metadata resources proved and reviewed | Coherent seven-conjunct era boot allocation proved; hardware ownership lifting pending |
| Register, device and disk ownership | Global dependent registers, device halves, reservations and complete disk-image laws proved | Native event WPs and interruptible event composition proved; exact lock camera linked; concrete lock callbacks proved; cyclic instruction-family and pool coverage pending |
| Filesystem image readers | Complete initial fsimg_wf (W1–W9), durable inode, links and full initial Snapshot.OK proved | Native filesystem hierarchy, link packing/gathering and root-slack camera allocation proved; guarded durable byte ledger proved; slot carving and crash transport pending |
| MachCSL adequacy and first closed slice | Closed JAL schedule-safety theorem builds over the actual eight-hart/device/power machine | Universal boot/cycle/worker proofs, eleven-fork handler and native adequacy linked; independent final review passed; two-hart TSO spinlock gate next |
| Kernel function proof port | Not started | Requires stable abstractions |
| Concrete input images and ELF parsing | Full hex/packed certificates, ELF loading, independent dumped-map and boot-image equality proved | Initial FS checker proved; Iris FS resource initialization remains open |
| Whole-system theorem closure | Not started | Requires all dependencies |

`docs/upstream/inventory.json` is an exhaustive lexical index of source files and
function families, not a proof coverage report. It deliberately marks every
reference source as `not_started`; partial ports will be mapped to exact source
symbols separately. A successful build cannot change whole-system status.

Recent findings: current upstream is newer than the paper (read-read relaxation,
icache, PID changes); paper is tagged `arxiv-v1`. Sequential Lean Sail V1 erases
barriers and cannot express required interleavings. Paper's Sail pin contains the
atomic A/D fix absent from the existing local theorem-labs RISC-V clone. Native
Iris has a real adequacy implementation; its apparent `sorry` occurrence is in a
comment, with transitive checking still required.



Validation at the initial published commit `329b04c`: [GitHub CI passed](https://github.com/theorem-labs/xv6-lean/actions/runs/34535032913).
The subsequent Sail integration [also passed GitHub CI](https://github.com/theorem-labs/xv6-lean/actions/runs/34535714841) with its own event/choice/conditional-write
regression suite. Current audits select the project by physical module/package origin, check
statement and proof/implementation dependencies, and reject unused/private axioms
and unreviewed computational hooks. Pinned Lean/Iris/Batteries/Qq implementation
boundaries are explicit. The closed whole-system root manifest remains empty.

The reviewed-plan/ELF/audit checkpoint `36d3860` [passed GitHub CI](https://github.com/theorem-labs/xv6-lean/actions/runs/34537520336).

The generated-model/ELF/execution checkpoint `3748ed5` [passed GitHub CI](https://github.com/theorem-labs/xv6-lean/actions/runs/34540305097).

Current machine integration is described in `MachCSL/Machine/STATUS.md`; device
source mappings and independent reviews are linked from their component status
files. These are structural and component proofs, not closed whole-system roots.

The concrete-machine/initial-ownership checkpoint `41eb69c` [passed GitHub CI](https://github.com/theorem-labs/xv6-lean/actions/runs/34543983862).

The whole-image correspondence checkpoint `2047134` [passed GitHub CI](https://github.com/theorem-labs/xv6-lean/actions/runs/34546951658).

The native allocation checkpoint `e955086` [passed GitHub CI](https://github.com/theorem-labs/xv6-lean/actions/runs/34549355945).

The native event/filesystem checkpoint `f8a1262` [passed GitHub CI](https://github.com/theorem-labs/xv6-lean/actions/runs/34551920513).

The current native spinlock safety and durable snapshot integration build
passes 972 jobs. Its complete project audit checks 26,065 logical declarations,
including 10,607 theorems, using only the three standard foundational axioms.
Forty-six compiler-generated total-recursion runtime companions are excluded
only as roots and remain forbidden in logical cones. The whole-system root
manifest remains empty. The initial-allocation audit checks all nine reviewed
caller edges and rejects additional runtime users. All twelve compiled audit
regression fixtures pass. The exact staged source has 739 reachable project
modules and passes all 87 generated-model pin checks.

All 21 pure initial snapshot clauses are proved against the actual disk bytes.
The native six-part `fsSnap` and existential `P_dur` now have checked initial
allocation rules, including exact byte carving, full inode/top/link resources,
root slack and the uncarved remainder. The literal image leaf instantiates
these rules with the checked snapshot and proves flattened home-byte equality
with the same physical `Image.disk`. A whole-import caller audit restricts
these pure-input constructors to reviewed initialization wrappers and leaves;
runtime snapshot readback, source-instance transfer and crash preservation
remain open. Initial allocation does not replace the current physical disk.

The complete seventeen-instruction spinlock family is preserved by the actual
generated Sail cycle, including both clock choices. Native event callbacks,
76-byte boot resource extraction, eight-way code sharing, cyclic hart WPs and
the eleven-worker boot handler compose into
`MachCSL.Logic.SpinlockMachineSafety.safe`. It proves reducibility and
observation consistency for every finite actual schedule from an arbitrary
powered-off generation-zero state, with the original durable medium and all
CPU, device and power interleavings. It has no handler or resource-contract
premise. This closes the safety part of the second small-program gate.

Operational holder exclusion remains open. Fable's fifth review requires
unique annotation updates fixed by the actual event; the concrete pool proof
is implementing that requirement. The separate positive execution proof is
constructing actual sub-instruction interference. Both exclusion and the
complete seven-message witness are required before the two-hart gate closes.
The all-view code-integrity lemmas are proved, but their preservation across
all annotated pool steps remains an application obligation.

`MachCSL.Logic.JalMachineSafety.safe` proves actual reducibility for every thread
in every finite reachable configuration, together with the model's observation
consistency predicate. Its only premises are the explicit platform parameters,
powered-off generation-zero initial state and actual machine schedule. Every
allowed boot witness, clock choice, CPU/device interleaving and power cycle is
covered. `concrete_positive_execution` supplies a platform, an initial state and
a positive fetched-JAL schedule with no premises. The boot medium is preserved.
This is the first small-program integration gate, not an xv6 or nontrivial TSO
resource-transfer theorem. See the component status and independent reviews.

The `7dceb3f` [hosted CI run](https://github.com/theorem-labs/xv6-lean/actions/runs/34554151319)
was cancelled by the 60-minute job limit during the cold build (583 of 762 jobs).
Its image-certificate modules took about two minutes each; no Lean failure was
reported before cancellation, and the audit steps did not run. The workflow now
allows 120 minutes for the cold image/model build and the complete audit suite.
This run is not recorded as a pass. Local build/audit results remain separate.

The `d6e1c8` [hosted run](https://github.com/theorem-labs/xv6-lean/actions/runs/34557164757)
also reached the old 60-minute limit during its build, with later audit steps
skipped. Newer runs use the expanded limit.

The expanded-timeout `9857e27` [hosted CI run](https://github.com/theorem-labs/xv6-lean/actions/runs/34558122240)
passed the complete build, proof/model audits, image tests and provenance
checks. It includes the closed JAL gate.

The actual boot resource extraction accounts for all 76 code/lock/counter bytes,
returns both exact residual maps, and supplies eight fractional code bundles.
The native protocol and code resources have separate independent reviews.
The earlier two-hart foundations commit `9fa51cd` [passed hosted CI](https://github.com/theorem-labs/xv6-lean/actions/runs/34559749537).

The full pure filesystem-image checkpoint `c9f2955` [passed hosted CI](https://github.com/theorem-labs/xv6-lean/actions/runs/34561944930).
The subsequent event-resource and native callback checkpoints remain pending
in hosted CI; local proofs and audit results are recorded separately.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
