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
| Production TSO memory port | Partial: core + 39 public lemmas | See MachCSL/Memory/STATUS.md for missing layers |
| Sail free V1 event interface | Implemented and independently reviewed | Pinned theorem-labs/lean-sail xv6-free-v1; generation/correspondence pending |
| Full generated Lean RISC-V model | Stock generation completed; free type/signature compilation passed | Full instruction compilation and correspondence pending |
| Machine/device/power language | Not started | Requires semantics contracts |
| MachCSL adequacy and first closed slice | Not started | Requires language and ownership |
| Kernel function proof port | Not started | Requires stable abstractions |
| Concrete input images and ELF parsing | Exact import, bounded byte proofs and ELF structural facts | Packed/list correspondence, loaded maps and FS initialization pending |
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

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
