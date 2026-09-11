# Actual register-node ownership WPs

`RegisterWPDefs/Spec/Proofs/Link` provide three native Iris NotStuck rules
for the actual dependent Sail register constructors, at paper artifact pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. They are direct-node ownership
specializations of `iris/HartRegNode.v:173–251`, composed with the register
ownership bridge from `iris/RiscvPtsto.v`. The full 410-line source file was
read before choosing this bounded interface.

`wp_read` takes the generation certificate, any fractional or discarded
register cell, and a guarded continuation consuming the same cell. The
actual read value is derived from the current state's authoritative
register interpretation. `wp_write` instead requires the full old cell;
it updates the actual current-era authority, preserves the complete fixed
state interpretation, and passes the full new cell to its guarded
continuation. The types are the generated `Register` and `RegisterType`,
including genuinely dependent values and continuations.

`wp_read_any` needs no register cell. Its guarded continuation must handle
**every** value of `RegisterType r`; it is instantiated with the actual
state's register value. This supports universally handled interrupt-pin
reads without creating or duplicating the PLIC's register fragments.

All three rules use `MachineInterp.generation_cases` against the actual
fixed authority. A stale generation yields a persistent death receipt
through `power_dead`; after the actual dead step, the proof invokes the
already proved native `wp_dead`. A current generation must be powered on.
The live branch uses actual `Step.hartLive` and the actual `NodeStep`
constructor. `read_step_unique` and `write_step_unique` invert every
possible actual successor, excluding the dead arm and recovering the exact
expression, state, empty observations and empty fork list. The write state
is linked by `EraState.writeBack_register`; the read state uses
`writeBack_focus`. No preservation oracle occurs in these WP interfaces.

The guarded continuation is used only after native `wp_lift_step` crosses
its required later. The invariant mask is closed again, the required
NotStuck reducibility witness is supplied, and the entire fixed state
interpretation and future observation trace are restored. Writes transport
observation well-formedness using the actual silent-step theorem. Native
step-credit accounting remains unchanged.

`RegisterWPSpec` is independently importable; `registerWPSpec` proves all
three fields. The four `registry*` exports use the existing final
twenty-slot registry and the supplied native invariant names. They have no
unproved callee-specification premise, allocate no new ghost slot, and use
the same `MachineInterp.irisGS`, image, fixed runtime names, whole trace and
arbitrary `Empty → IProp` postcondition as `DeadThread.threadWP`.

Validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.RegisterWPLink
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/RegisterWPAudit.lean
```

The 424-job build passes without warnings; the proof module takes about
1.3 seconds and the link 0.9 seconds. The audit traverses all 28 public and
private namespace declarations and permits only `propext`,
`Classical.choice`, and `Quot.sound`; its output is saved in
`/tmp/xv6-lean-research/register-wp-axioms.log`. No `sorry`, custom axiom,
`native_decide`, or `bv_decide` is used.

This does not yet port the source's general `mctx`/projection/resumption
interface, client-selected invariant-opening windows, `swp` wrappers,
hooked register writes, or the arbitrary-fraction same-write rule. It does
not establish a live hart loop, initial pool WPs, kernel safety, or final
adequacy. Those larger statements must be proved using this actual machine
instance and additional source rules.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
