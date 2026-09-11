# Independent closed JAL machine-safety review

Result: **PASS.** Reviewed frozen
`MachCSL/Logic/JalMachineSafety{Defs,Proofs,Link}.lean` and its status record,
including the closed handler linkage and positive execution witness. The reviewer
did not implement these three final gate files. The reviewer did implement the
previously reviewed generic `MachineAdequacy` dependency, so this review treats
that dependency as an existing contract and checks its final instantiation.
No implementation correction or edit was required.

## Final theorem and actual semantics

`safe` is universally quantified over `Platform`, an actual initial `State`, and
every finite observed `PoolSteps jalImage` schedule beginning at `[power]`.
Its only initial-state hypotheses are power off and generation zero. Its
conclusion gives an actual `Machine.Step` successor for **each** thread in the
final pool, together with `ObservationsOK` for that same run and final state.
There is no remaining boot-handler, worker-WP, ghost ownership, native world,
runtime-name, reducibility, or initial-register premise.

`Platform` has precisely two fields in the actual extras implementation:
`match_reservation : Arch.pa → Bool` and `valid_reservation : Unit → Bool`.
The theorem covers every choice. The concrete witness supplies both functions,
so it does not depend on inhabiting an unspecified platform class.

The boot image is the existing `jalImage`: byte `0x6f` at `0x80000000` and zero
elsewhere, with that address as reset vector. The theorem uses the same
image-parametric `Machine.Step`, `language`, `PoolSteps`, boot program, RAM
construction, eight harts, UART/PLIC/Virtio devices, TSO/reservation rules, and
power transitions as the rest of the machine development. No alternate
transition predicate or special progress constructor is introduced.

The proof directly instantiates the generic native strong-adequacy adapter.
`boot_initializer` discharges its final client premise using the separately
reviewed complete eleven-worker handler in the native `InvGS` supplied by
adequacy. It does not allocate or select a second invariant world. The concrete
namespace siblings have a checked observation/UART separation proof. The
complete template's zero names and empty image are ordinary auxiliary data;
the actual era allocator supplies machine resource names and its memory image.
No ownership of those placeholder names is asserted.

## Disk scope and non-vacuity

`safe_sized` establishes the same operational conclusion for every explicit
initial disk-prefix size. Allocation refers to the actual initial durable disk.
`safe` chooses size zero solely for internal ghost bookkeeping. This neither
changes the machine's disk nor restricts the universally quantified initial
state or its transitions. Because this client proves only safety, it can discard
the initial disk fragments. No disk-content theorem is obtained by treating the
empty prefix as a description of the whole medium.

`positive_fetched_execution` uses the existing actual execution theorem to take
a power-on step, fork all eleven workers, restart hart zero, fetch and retire
JAL, and return it to its loop. The schedule has more than one step and retains
the power thread plus all eleven workers. The named final state is
`fetchedJalState initial`, whose previously checked register theorem gives reset
PC/nextPC and `minstret = 1` for hart zero. The witness preserves the initial
durable disk. It is a chosen legal schedule; the safety theorem covers every
legal schedule, rather than restricting them to this witness.

`initialState` supplies power-off/generation-zero states for every device state.
`initialState_positive_execution` removes the initial-condition premises.
`concrete_positive_execution` additionally supplies `examplePlatform` and
`Devices.initial`, leaving **no premise**. Thus both the initial conditions and
the positive actual execution are inhabited; the gate is not justified by an
empty initial pool or an impossible schedule premise.

These results meet the early one-instruction machine-gate shape in
`docs/THEOREM_TARGETS.md:193–224`, including the shared machine family,
non-vacuity, and common native adequacy. The source context is the all-schedule
power adequacy conclusion in pinned `iris/RiscvAdequacy.v:1499–1617`, at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

## Independent validation and limits

```text
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.JalMachineSafetyLink
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/JalMachineSafetyIndependentAudit.lean
```

The independent build passed 519 jobs, with only the existing unused CPU-binder
linter warning in `JalBootResourcesShare`. The fresh physical-module-origin
audit checked all 38 logical declarations across the three gate and three
handler modules, including private helpers and complete statement/proof
dependency cones. Only `propext`, `Classical.choice`, and `Quot.sound` occurred;
no unsafe or partial semantic dependency was found and zero runtime companions
were excluded. Direct axiom checks of `safe`, `positive_fetched_execution`, and
`concrete_positive_execution` passed. Printed theorem types independently
confirmed the stated remaining premises and the premise-free concrete witness.

This is a closed safety gate for the actual generated-model JAL machine, with
the stated platform parameters. It does not imply fairness, eventual progress
of a selected hart under every schedule, the xv6 kernel theorem, filesystem
correctness or crash durability, a general client trace predicate, or checked
cross-prover correspondence of the full generated model. The status preserves
those boundaries.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
