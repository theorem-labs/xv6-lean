# Closed fetched-JAL machine gate

`JalMachineSafety{Defs,Proofs,Link}` closes native adequacy for the four-byte
`jal x0, 0` image at `0x80000000`. The theorem uses the same eight-hart,
UART/PLIC/Virtio, power-cycle, TSO, reservation, and generated Sail event machine
as the image-parametric kernel development.

`safe` has only these parameters and hypotheses: the source's two platform
predicates, an actual initial state with power off and generation zero, and an
actual finite observed `PoolSteps` execution from the singleton power thread.
It concludes `SafeConfiguration`: every thread in the resulting pool has an
actual `Machine.Step` successor, and that run's observations satisfy
`ObservationsOK`. It leaves no boot initializer, worker specification, arbitrary
ghost registry, invariant world, runtime ghost name, initial ownership, selected
boot register file, or proof of reducibility as an assumption.

The result covers every finite admitted interleaving and every permitted boot,
including arbitrary preboot registers, all eight workers, both clock choices,
counter wrap, independent PLIC pin reads, all permitted TSO views, device steps,
power-off, and subsequent power-on. It is a safety theorem; it does not assert
fair scheduling or eventual instruction execution on every schedule.

The linked boot handler allocates the actual worker resources and proves all
eleven fork WPs. Native strong adequacy supplies the invariant world; the handler
uses that same world. The concrete namespace siblings have checked observation
versus UART separation. `template` is a complete era record of auxiliary data;
zero names and its empty placeholder image are not assertions of ownership.
Actual era allocation replaces all machine-owned names and the memory image,
while unused kernel-layer auxiliary names carry no resource claims.

`safe_sized` proves the same result for every explicit initial disk-prefix size.
Its initializer receives fragments of the actual initial medium; this JAL client
can discard them affinely. `safe` specializes the internal proof bookkeeping to
size zero, without changing the initial physical disk, the machine semantics,
or the theorem's arbitrary-disk scope. No disk-content or durability conclusion
is inferred from that specialization.

The initial-state and execution premises are inhabited. `initialState` is a
concrete powered-off generation-zero state for every device state.
`positive_fetched_execution` uses the existing checked execution to power on,
fetch and retire JAL on hart zero in more than one actual step, leaving the power
thread and all eleven workers in a safe final pool and preserving the initial
disk. `initialState_positive_execution` supplies the initial conditions.
`examplePlatform` supplies the two Boolean predicate functions, and
`concrete_positive_execution` instantiates both platform and device state with
no remaining premise. The witness chooses one permitted boot; the general
safety theorem does not restrict all boots to that witness.

The proof combines the source-shaped native adequacy and power rules with a
concrete JAL client. It satisfies the early machine-gate contract in
`docs/THEOREM_TARGETS.md`. It does not prove the paper's xv6 kernel roots,
filesystem correctness, a durable crash predicate, a general client trace
predicate, or checked cross-prover correspondence for the complete generated
model. Those remain distinct source-port obligations.

Validation: the concrete link build passed 519 jobs. The fresh physical-origin
audit covers all 38 logical declarations in the three gate and three linked
boot-handler modules, including private helpers, and their complete statement
and proof dependency cones. It accepts only `propext`, `Classical.choice`, and
`Quot.sound`; no unsafe or partial logical dependency and no runtime-root
exclusion occurs. Both the universal safety theorem and the premise-free
positive witness have only those three axioms. Records are
`/tmp/xv6-lean-research/JalMachineSafetyAudit.lean`,
`jal-machine-safety-audit.log`, and `jal-machine-safety-build.log`.
Independent review of the final gate passed with a separate 519-job build and
38-declaration physical-origin audit; see docs/reviews/jal-machine-safety-review.md.
The integrated repository build passed 822 jobs and its full audit checked
23,108 logical declarations, including 8,616 theorems.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
