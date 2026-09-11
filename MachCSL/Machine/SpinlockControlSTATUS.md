# Spinlock hart selection and control instructions

The actual CSR instruction copies mhartid into x5 under machine privilege,
with every other input register arbitrary. The two branch plans cover both
Boolean outcomes of x6==0 and x15!=0. Their taken targets are the park and
retry addresses, respectively; an untaken branch preserves the complete
register file. Both actual JAL instructions update nextPC to the exact loop
or park address and suppress writes to x0.

A generic jump plan covers all seventeen aligned instruction addresses
under the actual reset misa value. CSR and jump certificates evaluate only
owned register events and are transported to arbitrary matching register
files. Signed backward-target arithmetic uses separate ordinary equality
certificates to avoid expensive elaborator conversion; Lean's kernel
checks each equality. No fixed hart number or branch-result assumption
narrows the exported instruction plans.

The component build passes 399 jobs, with the proof module taking about
2.3 seconds. Independent review and complete dependency audit passed for
all 37 declarations, standard three axioms only, no unsafe/partial dependency
and zero exclusions. See `docs/reviews/spinlock-control-review.md`.
These are individual execution plans; whole-cycle static preservation,
event composition and two-hart safety/exclusion remain separate work.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
