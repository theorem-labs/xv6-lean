# Fixed observation invariant

ObservationInvariantDefs/Spec/Proofs/Link use the existing observation-half
camera and native namespace invariants. The fixed invariant stores obsLedger R
and survives era replacement. Allocation consumes the client's actual history
fragment and R at that history. No additional camera or assumed trace property
is introduced.

The update rule opens only its supplied namespace, agrees the stored history
with the state's authority, invokes the client's ledger update at the reduced
mask, updates both history halves and closes the invariant. Timelessness of R
is explicit. A frame S is retained, allowing UART ghost state in permits.
The trivial predicate permits arbitrary next histories; callers still prove
actual-step ObservationsOK when reconstructing full stateInterp. It is not an
output-protocol or crash-consistency claim.

Validation: 382-job ObservationInvariantLink build passes. The final twenty-slot
registry wrapper supplies native invariants. Independent review passed (docs/reviews/observation-invariant-review.md);
all 18 declarations were checked. The combined root physical audit with
PowerWP checked 31 declarations, with only standard foundational axioms.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
