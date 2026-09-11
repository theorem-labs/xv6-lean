# Whole-pool coverage review

The coordinator read the eight modules from occurrence uniqueness through
the final coverage dispatch. An independent audit checked all 90 physical
declarations, full opaque bodies and referenced constructors; only the three
standard Lean axioms occur, with zero exclusions. The linked build passed
540 jobs.

The occurrence argument uses the invariant's exact eight-current-hart
permutation to show that every other live occurrence has a different CPU.
Actual hardware steps preserve those harts' registers, reservations and views;
log extension preserves their winning receipts. The owner effect laws show
that a selected update either leaves an existing other holder unchanged or
makes that other-holder case impossible. Selected-hart progress is established
for each actual event and each blocked or successful arm.

Code preservation follows from the event plan's exact request eligibility:
all writes target the lock or counter. Hart steps retain devices, and the
previously reviewed worker and power proofs handle the remaining scheduler
choices. The final Covers theorem discharges all preservation premises and
inhabits SpinlockPoolSpec; it takes no client-supplied correctness callback.

The separate boundary corollary was peer reviewed. It requires an actual
current-generation occurrence with residual pure unit, plus a physical PC at
one of the four body instruction boundaries. It makes no assertion about PCs
inside an instruction continuation. Its four declarations passed an independent
full dependency audit.

The coordinator also reviewed the three schedule and reachability modules.
ScheduledEvent records the actual occurrence index, selected successor,
physical post-state, observations and forks. ScheduledStep requires both the
actual hardware step and its graph annotation. Functionality holds without
an invariant premise. Every actual finite PoolSteps execution obtains this
schedule and its unique annotation with exactly the original count,
observations and erased endpoint. The holder theorem therefore covers all
actual finite executions from an arbitrary powered-off generation-zero state.

The direct reachable_boundary_exclusion corollary takes only actual PoolSteps,
physical expression membership and the two boundary PCs; it constructs the
labels and invariant internally. The final independent audit checked all 142
declarations across the eleven coverage/schedule/reachability modules, with
the same standard axioms and zero exclusions. The linked build passed 545 jobs.
Coverage, arbitrary-run exclusion, schedule uniqueness and the direct boundary
corollary are approved. The complete positive interference witness remains a
separate gate obligation.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
