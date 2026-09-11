# Independent root review: lock product and registry links

Verdict: PASS. Codex root read the complete Lock definitions, specification,
proofs and registry link, plus FsTopLink, against the pinned source camera
and ownership definitions in `Xv6Cameras.v` and `WpLock.v`.

The lock camera retains both authoritative components: optional CPU/marker
state and acquisition position. Matching authority and fragment agree on
both; neither exclusive fragment nor authority can be duplicated. Updates
and allocation use the native ExclAuth product laws, and the arbitrary
resource frame is preserved. The hidden-position wrappers existentially
retain the source field. These are algebraic operations, not lock
instruction specifications or proof of a holder protocol.

The registry adds the actual lock product at 24 and the existing complete
node map at 25. Earlier indices and later unused indices are preserved.
All inherited ledger, heap, era, disk, power, observation, invariant and
UART capacities use their original slots. Actual InvGS is constructed
from the same invariant columns. The distinct sleeplock camera remains
unimplemented; the new capacity does not claim to instantiate the entire
source lockG class.

A fresh separate audit passed for all 194 declarations in the five new
modules and their complete type/body dependency cones. Only the standard
three axioms occur; no unsafe/partial dependencies and zero exclusions.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
