# Dead-generation native WPs

`DeadThreadDefs/Spec/Proofs/Link` implement source `thread_gen` and
`RiscvExec.wp_dead` (`iris/RiscvExec.v:198–263`) at paper pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. This is an actual native Iris
NotStuck WP over the concrete machine language and its fixed state
interpretation. It is not a separate toy self-loop language.

`threadGeneration` returns the generation of hart, UART, disk and PLIC
workers, and `none` for the power thread. Its five projection theorems cover
all constructors. `dead_step` constructs the actual machine's corresponding
dead arm. `dead_step_unique` inverts **every** actual `Step` from a worker
that is not live, ruling out each live arm and proving exact equality of the
expression/state, no forks and no observations.

`stateInterp_dead` derives the strict bound `generation < g.generation`
from the fixed interpretation's actual authoritative generation counter
and the persistent death receipt. This is the authority/receipt argument
of source `wp_dead`; it is not a pure assumption that an arbitrarily chosen
state is dead. The strict bound refutes actual `ThreadLive`.

`wp_dead` uses native guarded `iloeb` and `wp_lift_step`. It preserves the
entire fixed state interpretation, shrinks/restores the invariant mask,
proves reducibility through `dead_step`, and uses `dead_step_unique` to
recover the same state and unchanged future trace. Only after crossing the
required step/later does it use the induction hypothesis. The native step
credit remains part of the lifting rule, just as in the source.

The result holds for every `Empty → IProp` postcondition, because the actual
machine language has no values. The four `wp_dead_hart/uart/disk/plic`
corollaries use the same theorem. It needs only a death receipt, with no
per-era resources. In particular it covers a dead hart even when its Sail
program would fail if live. It does not change `Step`, provide a live-thread
stutter, prove a power-thread WP or show that live hardware errors are safe.

The generic theorem accepts the actual `MachineInterp.Capacity`, image,
fixed runtime names, whole trace and native `InvGS_gen`. `threadWP` installs
precisely `MachineInterp.irisGS` for those arguments and `NotStuck` at the
full mask. The independently importable `DeadThreadSpec` states the rule.
The link instantiates it at `Invariant.registry` with `Names.native` using
the explicit native invariant capacity. `registryDeadThreadSpec` and
`registry_wp_dead` contain no unproved component-specification premise.
No new resource slot or alternate machine instance was introduced. The
native name constructor itself remains data; its world allocation is
proved separately by the invariant layer.

Validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.DeadThreadLink
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/DeadThreadAudit.lean
```

The 382-job build passes; the proof module takes about 1.0 seconds and the
link about 0.7 seconds. The independent all-declaration transitive namespace
audit checks 38 declarations and accepts only `propext`, `Classical.choice` and `Quot.sound`, including
the complete native WP/guarded-induction proof cone; output is
`/tmp/xv6-lean-research/dead-thread-axioms.log`. No `sorry`, custom axiom,
`native_decide` or `bv_decide` is used.

The live worker lifting rules, device/client invariants, power-thread WP,
initial thread-pool WPs and final machine/kernel adequacy remain separate
work. Source call sites enter this rule only after the generation authority
has justified the death certificate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
