# Machine language status

The source is `iris/RiscvLang.v`, `RiscvModelBytes.v`, `ArchReset.v`, and
`PowerBoot.v` at the paper's `arxiv-v1` commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
This directory defines the actual generated Sail CPU, concrete devices and power
rules as an Iris language. It does not prove xv6 safety or MachCSL adequacy.

| Source component | Lean files | Checked scope |
| --- | --- | --- |
| `mnode_step`, `riscv_step` | `Node`, `NodeProofs` | Sub-instruction events, shared-view TSO reads, writes, blocking, reservations, fences and generated cycle restart |
| `gstate`, `hart_step` | `State`, `NodeInvariants` | Complete memory bookkeeping and reservation preservation for hart steps |
| `uart_step`, `plic_step`, `disk_step` | `DeviceSteps`, `DiskSteps` | Concrete autonomous devices, total-view DMA, capture, drain, malformed-chain wild writes and interrupt wires |
| `pma_boot*`, board/reset program | `Platform`, `BootProgram` | Exact PMA table and actual generated initializer |
| Auxiliary `run` | `Run`, `RegisterRun` | Finite free-event execution and sound register evaluator |
| Boot witness | `ColdBoot`, `ColdBootFacts` | Actual initializer succeeds for every vector/hart ID; checked PC and MISA postconditions |
| RAM image and boot predicate | `Image`, `Boot` | Exact domain/content normalization, concrete witness without restricting existential pre-boot registers |
| Power rules and `prim_step` | `Power`, `Language` | Eight harts, three devices, arbitrary power cycles, generation death and durable-disk preservation |
| Actual fetch | `FetchRun`, `FetchJal`, `FetchIntegration` | Sound event evaluator; actual power-on forks eleven workers and a nonempty Iris schedule fetches/retires JAL on CPU 0 |
| Observable histories | `Observations`, `ObservationCycles`, `DevicePreservation` | Full source trace alternation, boot count, wire tie and cycle decomposition under arbitrary finite schedules |
| Structural invariants | `Invariants`, `Reachability` | Memory/reservation preservation under all primitive steps and arbitrary finite Iris thread schedules |

`language image` is an explicit Iris `Language` value with no values. The same
image parameter serves the small machine-code gate and the eventual xv6 theorem.
Two source platform reservation predicates remain explicit through the generated
model's `Platform` class. There is no arbitrary hart stutter: errors and discard
are stuck, and reservation blocking retains exactly the source computation and
state. Device idle rules follow the source.

Power-on constructs a real boot execution and forks eleven actors. Power-off
increments the generation; old actors subsequently stutter as dead threads.
Reboot resets devices and volatile RAM while preserving the current durable
disk, including changes made by prior drain steps. It does not reload fs.img.

Disk transitions publish one log entry exactly when their RAM write set is
nonempty. The reservation guard permits idempotent overlap, as in the source;
it is not strengthened to disjoint write domains. All transition classes preserve
`MemoryOK` and `ReservationsOK`. These structural properties impose no queue or
filesystem invariant and do not imply that a live hart can take its next step.

Representation changes remain explicit: total dependent Lean register files,
finite-domain functional byte maps, natural timestamps and Lean bitvectors.
`Memory/FiniteMap` supplies checked Lean map representation bridges; a source
Rocq-to-Lean simulation remains outstanding. The generated compiler/model audit
also remains distinct from cross-backend correspondence.

Validation uses `python3 tools/lake.py build` and the root transitive proof and
implementation audit. Independent source reviews are recorded in
`docs/reviews/machine-node-review.md`, `device-fabric-review.md`,
`boot-review.md`, `fetch-review.md`, `observations-review.md`, and the device review records. The first closed machine-code
adequacy gate, MachCSL state interpretation, ownership lifting, and kernel proofs
remain open.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
