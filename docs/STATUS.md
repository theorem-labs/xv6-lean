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
| TSO ownership | Native byte/timestamp, log, view, dirty-set and full heap metadata resources proved and reviewed | Coherent era allocation and all-view clean/dirty context load proved; registered ordinary store and physical stack laws proved; virtual memory ownership in progress |
| Register, device and disk ownership | Global dependent registers, device halves, reservations and complete disk-image laws proved | Complete two-hart spinlock gate proved and independently reviewed; supervisor kernel resources next |
| Filesystem image readers | Complete initial fsimg_wf (W1–W9), durable inode, links and full initial Snapshot.OK proved | Native allocation, readback, source-instance transport and cloning proved; runtime bootstrap and crash preservation in progress |
| MachCSL adequacy and first closed slice | Closed JAL schedule-safety theorem builds over the actual eight-hart/device/power machine | JAL and inhabited two-hart TSO spinlock gates closed; all six whole-xv6 roots remain open |
| Kernel function proof port | Exact mycpu bytes/decodes and native context load/register-fold prerequisites proved | Native PMP/interrupt rules and physical context stores/stack proved; translation and full function WP next |
| Concrete input images and ELF parsing | Full hex/packed certificates, ELF loading, independent dumped-map and boot-image equality proved | Initial FS checker and native resource allocation proved; live boot installation remains open |
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

The complete inhabited spinlock gate and native kernel/filesystem prerequisite
build passes 1,135 jobs. The complete audit checks 28,603 logical declarations,
including 12,202 theorems, with only the three standard foundational axioms.
Fifty-six compiler-generated total-recursion companions are excluded only as roots and
remain forbidden in logical cones. The initial-allocation caller check retains
exactly nine reviewed edges. All twelve compiled audit fixtures pass. The
reviewed staged source contains 902 reachable project modules and passes all
87 generated-model pin checks. The whole-system root manifest remains empty.

All 21 pure initial snapshot clauses are proved against the actual disk bytes.
The native six-part `fsSnap` and existential `P_dur` now have checked initial
allocation rules, including exact byte carving, full inode/top/link resources,
root slack and the uncarved remainder. The literal image leaf instantiates
these rules with the checked snapshot and proves flattened home-byte equality
with the same physical `Image.disk`. A whole-import caller audit restricts
these pure-input constructors to reviewed initialization wrappers and leaves;
full native snapshot readback now reconstructs all validity clauses from the
resources and returns those same resources. Source-instance transfer and snapshot
cloning are proved; crash preservation remains open. Initial allocation does not
replace the current physical disk.
Native transport now has checked mixed-fraction run laws and bidirectional
whole-footprint/run correspondence. The logged filesystem view is connected
to the existing signed byte camera at its own runtime name. Same-name
installation returns the exact unused-byte remainder. Source-instance transport
reads its minting facts from existing native ownership and preserves that
source; snapshot cloning retains the original at its original names. Coverage,
record decoding, exact signed block sets and logged-era installation provide
checked prerequisites for runtime configuration bootstrap. The native bitmap resource and inode-region record/marker allocation prelude
are now proved, preserving the actual supplied logged bytes. Full inode slots,
bitmap/cache/log invariants and crash preservation remain later layers.

The complete seventeen-instruction spinlock family is preserved by the actual
generated Sail cycle, including both clock choices. Native event callbacks,
76-byte boot resource extraction, eight-way code sharing, cyclic hart WPs and
the eleven-worker boot handler compose into
`MachCSL.Logic.SpinlockMachineSafety.safe`. It proves reducibility and
observation consistency for every finite actual schedule from an arbitrary
powered-off generation-zero state, with the original durable medium and all
CPU, device and power interleavings. It has no handler or resource-contract
premise. This closes the safety part of the second small-program gate.

Operational holder exclusion is proved for every actual finite execution.
Complete coverage includes other-hart and occurrence preservation, all worker
and power cases, and every permitted boot witness. Annotation updates are
unique for the same explicit occurrence-indexed actual schedule, as required
by Fable's fifth review. A direct physical-machine corollary excludes two
current harts at completed-instruction boundaries in the four body instructions;
it does not make an interior-continuation PC claim.

The positive execution proves actual boot, both fetched setup sequences,
CPU 0's zero reservation and a separately counted CPU 1 blocked read. It
reaches a real completed body boundary where the operational holder predicate
is true. That same execution continues through CPU 0's counter write, CPU 1's
held-lock reservation, CPU 0's blocked unlock, and the failed/successful retry
sequence. Exactly seven writes leave lock = 0 and counter = 2, with no
reservations, all twelve pool entries and the original durable disk.

`MachCSL.Logic.SpinlockIntegration.complete_gate` combines that same recorded
schedule, its inhabited holder checkpoint, unique annotation, native safety
and final facts. Independent source/dependency review passed all 30 final
holder/gate declarations. This closes the second small-program gate and
addresses Fable's sixth review. The witness fixes one platform, non-ticking
cycles and minimal ordinary views, has no power cycle, and leaves six CPUs
unscheduled. Active unlock continuations remain pending. These restrictions
do not narrow the separately proved universal safety and exclusion theorem.
See the final Fable disposition and spinlock-complete-gate-peer-review.md.

Kernel work now follows the exact disabled-SIE mycpu boundary. All fourteen
mixed-width instructions and all 32 actual ELF-backed bytes are checked,
including the actual compressed expansions under source supervisor settings.
Native running-context loads preserve the full heap/TSO and byte resources
for every permitted view, including own-author dirty forwarding. The finite
register fold preserves source fractions and pays actual register subevents.
The actual supervisor PMP and interrupt-suppression subprograms now have
native finite-register WPs. Ordinary registered context stores and physical
word/stack save/readback/rejoin rules are proved. Translation/A-D/TLB behavior,
virtual stack/tier assertions and enclosing cycle composition remain required
before a complete function WP is claimed.

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
The event-resource checkpoint `c22a247` [passed hosted CI](https://github.com/theorem-labs/xv6-lean/actions/runs/34563919603).
The callback checkpoint `72836cb` [passed hosted CI](https://github.com/theorem-labs/xv6-lean/actions/runs/34565105437).
The closed spinlock-safety checkpoint `6555da6` [passed hosted CI](https://github.com/theorem-labs/xv6-lean/actions/runs/34567416068).
The readback checkpoint `c251f55` [passed hosted CI](https://github.com/theorem-labs/xv6-lean/actions/runs/34568961728).
The operational-exclusion checkpoint `fa3b8ad` [passed hosted CI](https://github.com/theorem-labs/xv6-lean/actions/runs/34570645072).
The inhabited gate `f252d3d` remains pending in hosted CI; local validation is
recorded separately.

The original Rocq artifact has been replayed successfully in an isolated
OCaml 5.3.0/Rocq 9.0.1 environment. All 2,104 tracked files are unchanged.
The compiler-derived local import union has 1,314 modules; all six source
statement queries and all six proof-assumption queries passed. Each proof
prints the same thirteen assumptions (ten Rocq primitives, two reservation
parameters and dependent functional extensionality). Raw evidence, hashes,
versions, exact statements and a portable parser are archived under
[docs/upstream/rocq-replay](upstream/rocq-replay/). This is a source replay and
scoped dependency baseline, not a complete declaration graph or Lean/Rocq
semantic correspondence certificate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
