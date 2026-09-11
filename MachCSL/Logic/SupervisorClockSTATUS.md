# Native value-agnostic supervisor clock

The four `SupervisorClock{Defs,Spec,Proofs,Link}` modules implement the
value-agnostic clock rule from `HartMCycle.v:329–590,693–715`, and the
optional-tick resource boundary from lines 883–946, at source pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The complete relevant source
clock spine, `MinstretInv` ownership definitions, `TimerCap` boundary, and
generated `Platform.tick_clock`/`clint_dispatch` were inspected.

| Source boundary | Lean implementation |
|---|---|
| Exactly three mutable clock registers | `clockRegisters`, `clockFootprint` |
| Preservation off the three mutable fields | `OffClock`, its reflexive/transitive/write laws |
| Finite all-read-result plans | `Framed`, `read_plan`, `write_plan`, `readonly_plan` |
| Exact changed-mip callback, including hardware-pin reads | `callback_plan`, `changed_plan` |
| MTIP and optional STIP updates | `clint_plan` |
| All inhibit/filter choices and counter overflow | `should_inc_plan`, `clock_plan` |
| Both actual clock choices | `optional_plan`, `wp_optional` |
| Native arbitrary fractional footprint preservation | `wp_clock` |
| Source existential full three-cell resource | `clockRes`, `clockRes_iff`, `wp_clockRes` |
| Implemented independent native contract | `Spec`, `actual`, `nativeSpec` |

`clock_plan fp rs` requires only that `fp` contains full ownership entries
for `mcycle`, `mtime`, and `mip`. Its actual program is the generated
`tick_clock ()`. Every register read is independently universally
quantified, including reads of clocks themselves and unowned configuration,
deadline, and PLIC-pin registers. The proof retains all emitted writes and
all counter, STCE and changed-mip branches. It uses the exact modular
64-bit increment and timer comparisons. No current privilege, `menvcfg = 0`,
zero counter, fixed deadline, or no-overflow hypothesis is imposed.

The native rule additionally requires key uniqueness in the finite
footprint, a real generation certificate, and the corresponding native
register cells. It returns the same footprint with its original fractions
at an existential successor file. Additional full, fractional or discarded
cells may be framed in the footprint. `OffClock` states that this **symbolic
footprint file** changes only the three clock fields; it does not claim
equality of unowned physical register values. The implementation folds the
actual individual generated read/write events with `RegisterPlan.fold`.
The caller supplies the genuine terminal continuation WP. No assumed
software correctness or resource-access callback proves the clock body.

`clockRes_iff` proves that the existential footprint is exactly the source
`clock_res`: three existential 64-bit values with full register ownership.
The reverse direction merely fills unowned symbolic fields with defaults;
it imposes no reset-state assumption on the actual machine. `wp_clockRes`
restores this resource for either supplied tick choice. It proves the
optional clock suffix; the enclosing `try_step`/retirement/fetch/instruction
and restart composition remain separate. No clock or retirement camera is
added, and no cell is made persistent by this layer.

The source's current `MinstretInv.v:341` defines `minstret_inv = emp`.
`clock_res` (349–350) and mutable retirement resources are linear and are
carried by `InstrBytes.pc_is:701–707`. They are not reopened as invariants
across a multi-event clock. `TimerCap.stimecmp_inv` is a separate invariant
on an arbitrary deadline. This value-agnostic tick does not need to open it:
its read continuation handles every possible deadline. Precise timer CSR
read/write rules and `mcounteren.TM`/S-mode capability packaging remain
separate tasks. The STCE branch is retained, including for the source
supervisor `MENVCFG_S` setting with STCE enabled.

There is a concrete existing cross-backend correspondence gap. Pinned Rocq
`model-xv6iris/rv64d.v:23011–23025` implements `should_inc_mcycle` and
`should_inc_minstret` with short-circuit `and_boolM`: the configuration read
is skipped when CY/IR is inhibited. Generated Lean
`LeanPaperStock/Platform.lean:532–540` emits the `mcyclecfg`/`minstretcfg`
read before applying Boolean conjunction. This proof preserves the actual
Lean clock configuration read even when inhibited. It does not erase that
event or assert exact equality with the Rocq event tree. The analogous
retirement read difference is recorded here but retirement is not part of
this clock proof. Full cross-backend correspondence remains unproved.

Validation: the final `SupervisorClockLink` target completed **431 jobs**.
A fresh physical-origin audit checked **37 logical declarations in all four
modules**, including opaque theorem bodies, private helpers and inductive
constructors. Only `propext`, `Classical.choice`, and `Quot.sound` occur;
there are no unsafe or partial logical dependencies and **zero exclusions**.
The actual clock plan, both-choice WP, existential resource wrapper and
constructed native contract were also checked with `#print axioms`.
Evidence remains outside the repository at
`/tmp/xv6-lean-research/SupervisorClockAudit.lean` and
`/tmp/xv6-lean-research/supervisor-clock-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
