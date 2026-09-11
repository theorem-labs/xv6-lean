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
| Register, device and disk ownership | Global dependent registers, device halves, reservations and complete disk-image laws proved | Native event WPs and interruptible event composition proved; exact lock camera linked; concrete lock callbacks pending |
| Filesystem image readers | Complete initial fsimg_wf (W1–W9), durable inode, links and full initial Snapshot.OK proved | Native filesystem hierarchy, link packing/gathering and root-slack camera allocation proved; durable byte carving and crash transport pending |
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

The current event/camera integration build passes 908 jobs. Its complete project audit
checks 24,858 logical declarations, including 9,834 theorems, using only the three
standard foundational axioms. Forty-six compiler-generated total-recursion
runtime companions are excluded only as roots and remain forbidden in logical
cones. The whole-system root manifest remains empty.

The latest reviewed layer proves all 21 pure initial snapshot clauses against
the actual disk bytes, including every inode record, indirect entry, bitmap bit,
owned block and home-map coverage condition. Native fractional filesystem byte
views and the complete arbitrary-node top camera are checked. This does not
allocate the source's native durable filesystem interpretation `P_dur`.

Native exclusive RAM reads and present-payload RAM writes now have checked WPs,
including actual blocked retries, reservation validity, TSO updates and view
receipts. The spinlock image has checked bytes, all seventeen actual decoder
and universal fetch plans, and seven straight-line register instruction plans.
Remaining instruction plans, lock resource transfer and operational holder
exclusion remain under implementation. The two-hart gate
requires all-schedule safety, exclusion and a concrete interference witness.

The native event-composition layer is now proved and linked, with explicit
eligibility for ordinary versus held-snapshot proof rules. The exact lock
product and top inode cameras occupy slots 24 and 25. Control instruction
plans and the generated cycle wrapper are checked, as is generic annotation
transport over the identical actual pool schedule. Concrete protocol callbacks,
instruction-family preservation and annotation coverage remain to be proved.

The native filesystem hierarchy now factors into byte footprints and ghosts,
with exact inode/link packing, same-name gathering and fresh initial link/top
allocation including root slack. Durable byte flattening/carving is the next
dependency of native `P_dur`; fresh ghost allocation is not a reboot transfer.

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
skipped. Newer runs use the expanded limit; their results remain pending.

The expanded-timeout `9857e27` [hosted CI run](https://github.com/theorem-labs/xv6-lean/actions/runs/34558122240)
passed the complete build, proof/model audits, image tests and provenance
checks. It includes the closed JAL gate. Later commits remain pending in CI.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
