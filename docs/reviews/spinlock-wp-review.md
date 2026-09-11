# Independent review of the native spinlock cycle and loop

Reviewer: OpenAI Codex subagent `lean_logic_audit`, independently reviewing
coordinator-authored `MachCSL/Logic/SpinlockWPProofs.lean`.

Result: **PASS**. `cycle` instantiates the actual native EventPlan fold with the
proved seventeen-boundary `SpinlockFamily.cycle_plan`, exact indexed code RAM
access and the fully implemented native protocol callbacks. Its continuation
receives the returned owned registers, entire code share, actual reservation,
protocol resource and proved successor family. The terminal expression is the
actual hart `.pure ()`, whose semantics restarts a cycle; no machine value or
atomic whole-instruction rule is substituted.

`loop` uses native guarded Löb induction. The existing restart rule consumes
`resvAny`, clears the actual reservation and guards a continuation quantified
over both clock choices. The resulting cycle restores all resources and a new
family before applying the induction hypothesis. The generation certificate
is persistent; neither register ownership, code fractions, reservation nor
counter/holder resources are duplicated. The existing invariant world and
machine interpretation are reused. All event successors, blocked retries,
PLIC-independent pin results and stale-generation behavior come from the
reviewed native leaf rules/fold, rather than an assumed preservation callback.

The family theorem quantifies over arbitrary boot-relevant register contents,
all eight hart IDs, symbolic counters including overflow and both AMO results.
The protocol retains separate AMO read/write boundaries. This native loop is a
safety/resource-transfer component. It does not itself prove operational
holder-window exclusion, the annotated-pool application contract, a complete
boot handler or the interference witness.

A combined rebuild with EventPlanHead passes 571 jobs. The fresh physical-origin
audit checked both declarations in this file and their full type/body/inductive
constructor cones. Only `propext`, `Classical.choice` and `Quot.sound` occur;
there are zero excluded runtime companions and no unsafe/partial dependencies.
Evidence: `/tmp/xv6-lean-research/SpinlockWPAudit.lean` and
`/tmp/xv6-lean-research/spinlock-wp-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
