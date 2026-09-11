# Project status

The full Lean port is **not complete**. No Lean theorem currently establishes xv6
whole-system safety or filesystem crash consistency.

| Workstream | Status | Current owner / next gate |
|---|---|---|
| Full paper reading | Complete (47 pages) | Codex coordinator and audit agents |
| Baseline audit | Paper tag identified | Exact pins and image hashes recorded |
| Independent design reviews | Both complete: approve with required changes | Claude Code, Fable 5.1, max effort; see reviews/fable-disposition.md |
| Reproducible repository/tooling | Implemented; initial GitHub CI passed | Build, imports, image decoding and source regeneration pass |
| Native Iris build and integration | Complete initial integration | Generic adequacy axiom audit passed |
| Production TSO memory port | Core, byte read/write and finite-map/reservation bridges proved | See MachCSL/Memory/STATUS.md for missing layers |
| Sail free V1 event interface | Implemented and independently reviewed | Absent-write payload behavior corrected from pinned Rocq source |
| Generic event execution and result transport | Proved initial composition/inversion laws | Actual handlers, blocked steps and restart rules implemented; correspondence pending |
| Full generated Lean RISC-V model | Compiled; six execution/reset entry cones audited; real fetched JAL execution proved | Two explicit reservation predicates; full semantic correspondence pending |
| Machine/device/power language | Concrete language implemented, including Virtio DMA and power | Boot execution and arbitrary-schedule memory/reservation/trace invariants proved; ownership in progress |
| TSO ownership | Native Iris byte/timestamp ledger, log, view and dirty-set resources proved and reviewed | Actual-state TSO interpretation and full boot ownership allocation proved; heap metadata and full state composition pending |
| Register and device ownership | Actual dependent register bridge and three device-half bridges proved and reviewed | Global eight-hart and full reservation ownership proved; whole-state integration pending |
| Filesystem image readers | Superblock, inode encoding/decoding, W3 and rounded-region predicates ported | Initial superblock/log, live-inode and all rounded-region checks proved; full filesystem initialization pending |
| MachCSL adequacy and first closed slice | Actual power-on and fetched-instruction schedule proved | Full ownership interpretation, lifting and adequacy pending |
| Kernel function proof port | Not started | Requires stable abstractions |
| Concrete input images and ELF parsing | Full hex/packed certificates, ELF loading, independent dumped-map and boot-image equality proved | Full FS initialization remains open |
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

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
