# Native machine adequacy adapter

Implemented in `MachineAdequacy{Defs,Proofs,Link}.lean`. This is an explicitly
conditional machine adequacy component, with concrete native Iris linkage. It
does not yet discharge the JAL boot handler or any xv6 boot handler.

## Contract and source correspondence

`BootInitializer` takes the full byte fragments of the actual initial state's
durable disk and the shared trivial observation invariant, at freshly allocated
fixed names and the run's whole trace. It must produce `PowerWP.bootHandler`.
The obligation is quantified over every supplied native `InvGS`, so the client
cannot choose a separate invariant world. `initializer_of_handler` covers a
handler established from the observation invariant alone, discarding the affine
disk fragments.

The handler itself quantifies over every actual `BootFacts`, including arbitrary
preboot registers, and owes the native WPs of all eleven forked workers. Neither
an arbitrary state-preservation oracle nor a pre-existing pool WP is assumed.
The initial pool is the real singleton `[power]`.

`not_stuck` instantiates native `wp_strong_adequacy_gen` with the actual
image-parametric machine language, zero additional laters per step, the existing
fixed `stateInterp`, and the trivial fork postcondition. It allocates fixed
machine resources through `MachineInterp.initial_off_alloc`, using the actual
`initial.devices.virtio.v_disk`, then installs the empty-history observation
ledger and applies `PowerWP.wp_power`.

The final continuation obtains native `NotStuck` for every thread in the final
pool. It opens the final state's own trace interpretation: the empty remaining
future forces its stored history to equal the actual schedule's observation
list. This yields `ObservationsOK`, including alternation, boot count, and the
current-cycle UART wire tie. `safe` converts `NotStuck` to existential actual
`Machine.Step` successors because this language has no values. The conclusions
quantify over every finite observed `PoolSteps` schedule, including all power,
hart, and device interleavings admitted by the actual semantics.

This adapts the machine-safety and final-history portion of pinned
`iris/RiscvAdequacy.v:1298–1617`, especially its `wp_strong_adequacy` invocation at
1512 and final state/history elimination. The upstream pin is
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The full source crash predicate,
projection/custody/lending hooks, arbitrary trace predicate, filesystem
durability, and kernel boot-resource contract remain separate work; this slice
does not claim those conclusions.

## Native world and registry discipline

Native `wp_strong_adequacy_gen` calls `fupd_finally_soundness`, which allocates the
world used by all WPs in this proof and accounts for the final soundness step
credit. The adapter reuses that supplied world. It deliberately does not nest
`StateAllocationLink.native_initial_off_alloc`, whose independently allocated
native names would establish a second world. Its application allocation is the
same already-proved generic component used by that wrapper.

`registryPreS`, `registry_not_stuck`, and `registry_safe` use the existing
`UartGhost` 23-slot registry and its explicit native capacity at slots 16–19.
All machine capacities and application slots remain unchanged. No new camera,
runtime-name assumption, or unproved component specification is introduced.

## Validation

```text
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.MachineAdequacyLink
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/MachineAdequacyAudit.lean
```

The build passed 429 jobs; the proof and link modules compiled in approximately
one second each. The fresh audit checked all nine new declarations and their
transitive axiom dependencies, accepting only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, new axiom, native decision procedure, or unsafe proof
mechanism was introduced. No existing allocation, power, or registry file was
edited.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
