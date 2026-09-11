# Native supervisor retirement boundary

This proposal ports the register-only setup and successful retirement
completion surrounding the actual generated instruction body. It also
packages the exact source `minstret_res` and `pc_is` ownership. It does not
assume a correct whole instruction or claim a fetched supervisor cycle WP.
The instruction body, translation, interrupt dispatch and stack accesses
remain separate, concrete proof obligations.

Source references are relative to `.upstream/xv6iris`, pinned to
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The generated Lean model is the
staged `LeanPaperStock` model from Sail source
`23dcf8fd923eb8a1958795393d2975632aa940b2`, using runtime
`28c729b5bb574ae7c32c13353403e57c575d85dd`. The native Iris pin remains
`728a17140939e49af9236f7cb0d037da9ec52435`. This review read the current
resource definitions, the setup/tick-PC lemmas, the complete successful
`swp_try_step_gen` proof and both clock-wrapper statements, and the full
actual generated `try_step` definition. Old explanatory comments are not
used to override their current definitions.

## Source resource and event correspondence

| Source | Exact obligation and native counterpart |
|---|---|
| `iris/MinstretInv.v:341` | `minstret_inv = emp`. Do not allocate a new invariant or camera. |
| `iris/MinstretInv.v:349–363` | `clock_res` owns full `mcycle`, `mtime`, `mip`; `minstret_res` owns full `minstret` and Boolean `minstret_increment`, plus discarded `mcountinhibit` and `minstretcfg` cells with existential arbitrary values. |
| `iris/InstrBytes.v:701–706` | `pc_is x` owns full PC and nextPC at the same `x`, both preceding bundles, and `resv_any cpu`. This contains seven mutable register cells, two discarded cells and one reservation fragment. |
| `iris/HartMCycle.v:64–70,103–124,272–276` | Read current privilege, calculate the IR/filter flag, write `minstret_increment`. No reset/configuration value or privilege regime is assumed. |
| `iris/HartMCycle.v:161–177,618–642` | `tick_pc` reads nextPC, writes PC, and reads PC again for its pure callback. Retain that final read event. |
| `iris/HartMCycle.v:747–879` | On actual `Step_Execute (Retire_Success, bits)`, validate active hart state, read hart state again, commit nextPC, read the flag, and conditionally read/increment minstret. The source wrapper assumes the instruction preserved the setup flag; the lower-level native completion rule can instead expose the actual post-body flag without that premise. |
| `iris/HartMCycle.v:278–282,886–946` | The source hides the final counter in `wrap_post`, then clocks either zero or one times while retaining all non-clock cells and indexed resources. A native exact counter equation can strengthen this intermediate result. |
| `iris/RiscvLang.v:222–224`; `MachCSL/Machine/Node.lean:51–54` | The actual cycle is `try_step 0 false` followed by the externally chosen optional clock, including both choices. Reservation clearing belongs to the separate restart node. |

The relevant generated definitions are `Platform.lean:538–547`,
`PcAccess.lean:218–220` and `Step.lean:406–481`. There is no separate
`tick_minstret` definition in this pinned generated model: its conditional
increment is inside `try_step`. A local proof-facing tail must therefore
be linked to that actual continuation by a checked equality.

The successful postlude has these distinct register events, in order:

1. Read hart state for the successful-retirement assertion.
2. Read hart state again to select waiting versus active completion.
3. On the active branch, read nextPC, write PC, and read PC for the callback.
4. Read actual `minstret_increment`.
5. If that flag is true, read actual minstret and write its 64-bit modular
   increment. Otherwise emit neither of these two counter events.
6. Return `false`. The pinned RVFI configuration is definitionally false;
   the post-step and instret callbacks are definitionally pure unit.

These are individually interruptible machine nodes. An owned fractional
active-hart cell justifies the two active-state reads; it is not a
postulated read-result oracle. Full counter and PC cells justify their
reads and writes. The flag is not cleared at completion. Its next change
is the next setup write or an independently proved instruction write.

There is an existing cross-backend event correspondence gap:
`model-xv6iris/rv64d.v:23020–23025` short-circuits the `minstretcfg` read via
`and_boolM` when IR inhibits counting. Generated Lean `Platform.lean:538–540`
reads both registers eagerly. The analogous clock-config difference was
already recorded in `SupervisorClockSTATUS.md`. The native proof must
retain both actual Lean reads. Equal Boolean results under pinned reads
do not establish equality of these event trees.

## Proposed ownership and pure API

Own new `MachCSL/Logic/SupervisorRetirement{Defs,Spec,Proofs,Link}.lean` and
`SupervisorRetirementSTATUS.md`, with an additional same-prefix factoring
module only if the checked generated continuation requires it. Reuse
`Registers.Capacity`, the existing era register names, `RegisterFootprint`,
`RegisterPlan`, `SupervisorClock` and `Reservations`; allocate no ghost
state and do not extend any registry.

The source packages are:

```text
retirementFootprint =
  [(minstret, own 1), (minstret_increment, own 1),
   (mcountinhibit, discard), (minstretcfg, discard)]
minstretRes regCapacity name =
  ∃ rs, RegisterFootprint.cells regCapacity name rs retirementFootprint

pcIs capacity era cpu x =
  regPointsto PC (own 1) x ∗ regPointsto nextPC (own 1) x ∗
  minstretRes capacity.era.registers (era.registers cpu) ∗
  SupervisorClock.clockRes capacity.era.registers (era.registers cpu) ∗
  Reservations.resvAny capacity.era.reservations era.reservations cpu
```

Prove these existential encodings equivalent to the direct source-shaped
cell assertions. Prove explicit split/join of their disjoint register
footprints. Neither construction allocates or duplicates cells. Additional
fractional hart-state/privilege cells belong to the ambient instruction
context, not to `pcIs`; the same register cannot appear twice in a combined
`Unique` footprint.

Use these symbolic register transformations:

```text
flag mc cfg priv = (IR mc == 0) && (counter_priv_filter_bit cfg priv == 0)
setupAfter rs priv = write rs minstret_increment
  (flag (rs mcountinhibit) (rs minstretcfg) priv)
tickPCAfter rs = write rs PC (rs nextPC)
completeAfter rs =
  if rs minstret_increment then
    write (tickPCAfter rs) minstret (BitVec.addInt (rs minstret) 1)
  else tickPCAfter rs
```

`setupAfter` keeps the actually read privilege explicit. The strongest
pinned variant specializes it to `rs cur_privilege` using an arbitrary
owned share of that cell. A second variant uses `RegisterPlan.readAny`
and covers every possible privilege result, with an existential result
index. Neither variant assumes Supervisor or Machine privilege.

The first plan theorems should be:

- `should_inc_plan`: actual `should_inc_minstret priv`, arbitrary pinned
  config shares, exact returned `flag`, unchanged symbolic file.
- `setup_plan`: actual extracted setup, full flag ownership and readable
  config/privilege cells, exact `setupAfter`. The old Boolean is arbitrary.
- `tick_pc_plan`: actual `tick_pc ()`, readable nextPC and full PC,
  exact `tickPCAfter`; no assumption that the old PC already equals nextPC.
- `complete_plan`: actual extracted successful postlude, a readable active
  hart-state cell, full PC/minstret/flag cells and readable nextPC, returning
  `false` with exact `completeAfter`. The completion flag and counter are
  arbitrary post-body values, including all overflow cases.
- Field consequences: final PC equals the incoming nextPC; nextPC, the
  flag and config cells are unchanged; the counter has exactly the above
  modular equation; all other symbolic fields are unchanged.

General plan theorems use any finite footprint containing their listed
members. `Unique` is required by the native writable fold. The exact
source packages specialize nextPC and the flag to full shares, although
read-only subprogram lemmas may accept arbitrary shares where sound.
Symbolic off-footprint equality is not asserted as ownership of every
physical register.

## Link to the generated tree and native WP

Extract the setup and postlude into local proof-facing expressions and
prove a kernel-checked factorization of **actual** `try_step` into setup,
its unchanged hart-state/body selection, and its complete original
postlude. The postlude factorization retains every `Step` arm, including
waiting, traps, illegal instructions and external failures. Only its
successful active branch receives a retirement plan in this slice. A
handwritten successful tail without this factorization would not suffice.
No generated model file changes are proposed.

The native `Spec` consists of the proved setup, tick-PC and successful
completion rules, with the ordinary `RegisterPlan.fold` continuation
shape. For completion, schematically:

```text
Unique fp → readableActiveHart fp rs → full/read members listed above →
generationCertificate -∗ cells rs fp -∗
  (cells (completeAfter rs) fp -∗ WP (continuation false)) -∗
  WP (actualSuccessfulPostlude bits >>= continuation)
```

Here `readableActiveHart` is a pure membership plus `rs hart_state = ACTIVE`
fact backed by the corresponding owned cell. `bits` is arbitrary. All
`WP`s are native actual hart-expression WPs under the existing machine
interpretation. The continuation is the real residual program after this
finite prefix, not an assumed WP for the instruction body. `Spec` must be
constructed from the native register rules in `Link`; no field is assumed
as a caller-supplied software contract.

Compose completion with `SupervisorClock.optional_plan`/its native fold
for both ticks. This preserves the exact completed PC, flag and minstret
while existentially repackaging the three clock values. Arbitrary
additional owned cells and indexed frame resources survive. The clock
continues to cover all configuration/STCE/pin/callback branches; do not
reuse the reset/MENVCFG=0-specific `JalLoop` clock transformation.

Provide a boundary-resource reassembly lemma: from the completed PC and
nextPC cells at `x`, preserved retirement/config cells, clock cells and the
original arbitrary reservation fragment, reconstruct `pcIs ... x`.
Register-only completion and clock operations leave that reservation token
framed. Clearing it requires the existing actual `RestartWP` node, whose
continuation quantifies over both future tick choices. This slice must not
pretend that terminal `.pure ()` is a terminal machine value or omit that
restart transition.

## Acceptance boundary and remaining work

Build the modules and audit every physical declaration, traversing types,
opaque proof bodies and inductive constructors. Permit only the standard
three Lean axioms; no native-decision axioms or custom computational hooks.
Check source-equivalent resource packaging, exact event factorization,
arbitrary-value plans and the native rules. The general modular counter
formula supplies the overflow result without requiring executable samples.

A completed checkpoint would establish actual retirement setup/completion
and source-shaped linear cycle resources. It would still not prove an
arbitrary `try_step` succeeds, prevent supervisor interrupts, validate an
instruction fetch, supply virtual stack mappings, or establish `mycpu`.
The next instruction-cycle assembly must discharge actual fetch/dispatch
and each instruction body, then use these prefix/tail rules compositionally.
It may derive the source flag-preservation premise for instructions that
preserve it; it may not assume that premise for arbitrary generated bodies.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
