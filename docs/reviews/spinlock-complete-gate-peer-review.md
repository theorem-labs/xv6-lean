# Independent review of the inhabited spinlock gate



Reviewer: independent `lean_logic_audit` Codex agent. The artifact agent
wrote `SpinlockWitnessHolderDefs/Proofs`; the coordinator wrote
`SpinlockGateProofs`. All three files were read completely. **PASS**, with
no production changes requested.

The holder witness reaches a real instruction boundary after CPU0's
successful AMO and its subsequent ADDIW/non-taken retry branch. The actual
residual program is `.pure ()` and its actual PC is instruction 10, the
counter load. `reach_local` and `leave_local` use checked generated
execution facts and the existing `NodeSteps` soundness rules; pool lifting
retains the other threads. The boundary's `Holds` assertion is derived
from the actual prefix annotation and the proved physical boundary rule,
not inserted as a fresh proof label or assumed predicate.

`annotated_holder` first annotates the actual powered-off-to-holder prefix.
It then lifts the actual suffix starting from that very annotated midpoint
using the proved whole-pool `covers`, and composes the two scheduled runs.
Thus the holder state lies on an actual run to the seven-message endpoint,
including the existing conflict/retry phases. Prefix and suffix lengths
are positive with the stated bounds, and their actual observations are
power-on and empty respectively.

`complete_gate` uses that same `preSchedule ++ suffix` in the final
`CertifiedRun`. It obtains actual machine steps by erasure, native safety
from the closed safety theorem, and uniqueness from the schedule
functionality theorem. It does not select an unrelated second annotation
for the final certificate. The current-holder uniqueness at the midpoint
uses `holder_exclusion` together with the actual CPU0 holder witness.
This closes the previously conditional holder-inhabitation point.

The endpoint retains twelve threads, lock zero, counter two, seven exact
message authors, cleared reservations, and the original durable disk.
Unlock continuations remain pending; no return from a higher-level xv6
release function is asserted. The existential witness uses the explicit
`SpinlockWitness.platform`, while the previously proved arbitrary-run
safety and exclusion results retain their broader quantification. The
other six CPUs are unscheduled in this witness. Neither fairness nor
termination under arbitrary scheduling is claimed.

The coordinator reported the target green at 666 jobs. A fresh independent
physical-origin audit checked all **30 declarations in three modules**,
with full opaque theorem bodies and constructor traversal, **zero
exclusions**, and only `propext`, `Classical.choice`, and `Quot.sound`.
No unsafe or partial dependency occurs in any logical cone. The annotated
holder, concrete holder and complete gate theorems were additionally checked
with `#print axioms`.

Evidence: `/tmp/xv6-lean-research/SpinlockGatePeerAudit.lean` and
`/tmp/xv6-lean-research/spinlock-gate-peer-audit.log`. This completes the
inhabited operational test-image gate reviewed here; it does not establish
the kernel's source acquire/release/holding interfaces.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
