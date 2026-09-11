# Native retirement and source cycle resources

`SupervisorRetirement{FactorDefs,FactorProofs,Defs,Spec,Proofs,Link}` is a
completed register-only prerequisite for actual supervisor instruction
cycles. It implements retirement setup, successful completion, optional
clock composition and the exact source `pc_is` resource partition. It does
not assert that an arbitrary fetched instruction retires successfully.

The source pin is `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. Relevant source
sections and the entire actual generated `try_step` were inspected; the
implementation boundary is recorded in
[`supervisor-retirement-boundary.md`](../../../docs/design/supervisor-retirement-boundary.md).
The generated model is the staged Sail-source
`23dcf8fd923eb8a1958795393d2975632aa940b2` model with free runtime
`28c729b5bb574ae7c32c13353403e57c575d85dd`. Upstream generated-model notices
remain in `models/riscv/LICENSES`.

| Source / actual model boundary | Native implementation |
|---|---|
| `MinstretInv.v:359–363` | `retirementFootprint`, `minstretRes`, `minstretRes_iff`: full counter/flag plus discarded inhibit/config, all values existential. |
| `InstrBytes.v:701–706` | `pcIs`: full PC/nextPC, retirement resource, exact `SupervisorClock.clockRes`, and original `resvAny`; seven full and two discarded register cells. |
| Same source ownership partition | `pcFootprint_unique`, `pcFootprint_split`, `pcIs_intro`, `pcIs_iff`, `pcIs_parts`: native split/join, with no ownership for unlisted fields. |
| `HartMCycle.v:64–70,103–124,272–276` | `flag`, `setupAfter`, `should_inc_plan`, `setup_plan`; `setup_any_privilege_plan` independently covers every unowned privilege result. |
| `PcAccess.lean:218–220`; `HartMCycle.v:161–177,618–642` | `tick_pc_plan`: actual nextPC read, PC write, final PC callback read, without old-PC/nextPC equality. |
| `Step.lean:406–481` | `setup`, complete original `postlude`, and `try_step_factor`: kernel-reflexive equality retaining every body branch and every `Step` outcome. |
| `HartMCycle.v:747–879` successful tail | `complete_plan`, `completeAfter`: both active-hart reads, tick-PC, actual post-body flag, conditional modular counter increment and false result. |
| `HartMCycle.v:278–282` | `complete_pc`, `complete_nextPC`, `complete_flag`, `complete_counter`, `complete_other`: exact resulting field equations. |
| `HartMCycle.v:886–946` | `complete_clock_plan`, `wp_complete_clock`, `completed_clock_pc`, `completed_clock_counter`, `pcIs_completed`: both clocks with exact non-clock results and boundary reassembly. |
| Actual individual register steps | `wp_setup`, `wp_tick_pc`, `wp_complete`, constructed `Spec`/`actual`/`nativeSpec`, using `RegisterPlan.fold`. |
| `clock_res` framed inside `pc_is` | `wp_clock_pcIs`: the full boundary resource survives either clock choice. |
| Actual machine restart node | `wp_pcIs_restart`: preserves the nine register cells, clears the owned arbitrary reservation to none, and guards a continuation for every next tick. |

The successful completion plan accepts arbitrary post-body `minstret` and
`minstret_increment` values. A true flag increments the 64-bit counter
modulo its width; a false flag emits no counter read or write. The flag is
preserved, not cleared. Both hart-state reads are pinned to active by an
explicit owned fractional cell. Configuration and privilege shares are
arbitrary in the setup plan; the source package specializes the two config
shares to discarded ownership. No reset counter, fixed privilege regime,
fixed inhibit bit, deadline or no-overflow premise is imposed.

`FactorDefs.postlude` transcribes the full continuation of generated
`Step.lean`, including interrupts, waiting, traps and all external failures.
`try_step_factor` is proved by `rfl` for every `stepNo` and `exitWait`.
Only the successful active continuation is proved reducible by this slice;
the other branches have not been removed or assumed successful. There is
no standalone generated `tick_minstret` definition: the proof links to the
increment inside that actual postlude. The pinned RVFI configuration is
false and the relevant callbacks are pure unit, while their required
register reads, including the final PC read, remain in the plan.

The optional clock uses the existing value-agnostic `SupervisorClock`
proof, including all STCE, configuration, overflow, timer and hardware-pin
branches. Its `OffClock` relation describes the symbolic footprint file;
it does not manufacture ownership of unlisted physical registers. Native
rules preserve every listed fraction and fold each actual subevent under
the existing machine interpretation. Their terminal continuations are the
actual residual hart WPs, not instruction-correctness or memory-access
oracles. `pcRegs` merely separates the register part for restart, avoiding
any duplication of the reservation token. No camera, registry slot, new
invariant, readonly conversion or initial allocation is introduced.

The reverse resource equivalences fill only unowned symbolic fields with
`zeroRegisters`. Every owned cell is filled with its independently supplied
value. This imposes no reset-state hypothesis on the actual machine.
The source `minstret_inv` remains `emp`; the linear counter and clock cells
are not put inside an invariant open across multiple events.

An existing correspondence limitation remains explicit. Rocq
`model-xv6iris/rv64d.v:23020–23025` short-circuits the `minstretcfg` read when
IR inhibits counting. Generated Lean `Platform.lean:538–540` eagerly reads
both inhibit and config. `should_inc_plan` preserves both actual Lean
reads. The analogous clock discrepancy is recorded in
`SupervisorClockSTATUS.md`. Equal Boolean results do not prove equality of
these Rocq/Lean event trees; full cross-backend correspondence is still
unproved.

Validation: `SupervisorRetirementLink` built successfully in **439 jobs**.
A fresh physical-origin audit checked **117 logical declarations in all six
modules**, including private helpers, full opaque theorem bodies, types
and inductive constructors. Only `propext`, `Classical.choice` and
`Quot.sound` occur. There are no unsafe or partial logical dependencies and
**zero exclusions**. The factorization, successful plan, exact counter
formula, source resource equivalence, clock/restart WPs and native contract
also passed explicit axiom queries. Audit evidence is outside the repo at
`/tmp/xv6-lean-research/SupervisorRetirementAudit.lean` and
`/tmp/xv6-lean-research/supervisor-retirement-audit.log`.

Supervisor fetch, interrupt dismissal, translation/TLB behavior, instruction
bodies and the complete `mycpu` function WP remain separate obligations.
This checkpoint provides their real register-only prefix and suffix; it
contains no whole-instruction correctness premise disguised as a plan.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
