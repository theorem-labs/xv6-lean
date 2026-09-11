# Native per-hart JAL recursion review

Root read EventWPJalLoopSpec, Proofs and Link. The guarded hypothesis is quantified
over symbolic owned registers, and it is used only after the actual restart
step's later modality. Restart clears and returns the reservation, both clock
choices are covered, and the cycle continuation returns the owned cells and code
resources before applying the hypothesis to the next register table.

The link discharges the cycle and restart contracts with native implementations.
No issue found. This older per-hart interface retains SnapshotCovered explicitly;
it is not the universal boot interface. EventWPJalUniversal separately removes
that premise using the OFF-only PMP proof and is the interface used by the actual
boot handler. The original 472-job build and independent ten-declaration audit
are recorded in the component status; the integrated build also passes.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
