# Exact first-event view of an interruptible plan

`EventPlanHeadDefs` and `EventPlanHeadProofs` provide a proof view of the
existing `EventPlan.Plan`. `Head` has nine constructors: pure return, owned
register read, universal pin read, owned register write, pristine/code read,
mutable plain read, exclusive read, present write and barrier. Each constructor
indexes the original program by its exact `.pure` or `.impure event k` tree;
the original-program equality is enforced by the type, not an extra assumption.
Every continuation remains an ordinary existing `Plan` with the same final
postcondition.

`head_of_plan` proves completeness by induction on the existing plan.
`prefix_head` decomposes the actual `EventWP.ExecPlan` prefix: a pure prefix
continues into its supplied continuation head, while an event retains the
remaining prefix and its real monadic continuation as the residual plan.
This also handles nested prefixes introduced by plan composition. `plan_of_head`
reconstructs the original plan, and `plan_iff_head` establishes equivalence.
No evaluator, runtime selection function or alternative machine semantics is
introduced.

The event cases preserve the exact existing interfaces. Owned register reads
use `rs r`; pin reads require every typed value and retain the symbolic register
file unchanged. Owned writes use the actual dependent `Registers.write` update.
Code reads retain the RAM/plain guards, exact `reads n req word` fact and
`Ok (word, none)` result. Mutable reads retain all relation-indexed returned
words, with plain reads preserving the reservation and exclusive reads
installing the actual snapshot. Present writes retain their full request,
selected ordinary/reserved mode and eligibility evidence, then clear the
reservation on success. Barriers preserve the reservation and expose every
relation successor. No successor is asserted to exist merely because a
relation-indexed head exists.

Additional inversion theorems expose pure postconditions, the owned/pin
register-read alternatives, register-write residuals, all three memory-read
alternatives, the exact write-mode/value residuals, and barrier residuals.
These can be combined with actual `NodeStep` inversion and separately proved
state/resource facts. They do not themselves justify a memory relation label,
a blocked retry, a machine successor, a concrete annotated-pool `Covers`
contract or an operational exclusion theorem. No machine event is removed or
restricted by this proof-view definition.

Validation: `python3 tools/lake.py build MachCSL.Logic.EventPlanHeadProofs`
passes all 393 dependency jobs; the proof module builds in 1.1 seconds. A fresh
physical-origin audit checked all 23 declarations in the two modules and their
full type/body/inductive-constructor dependency cones. Only the allowed
standard axioms occur, with the exported decomposition/inversion roots using
`propext` alone. No unsafe/partial logical dependency was found and zero
declarations were excluded. No `sorry`, custom axiom or native decision proof
is used. Audit driver/log: `/tmp/xv6-lean-research/EventPlanHeadAudit.lean` and
`/tmp/xv6-lean-research/event-plan-head-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
