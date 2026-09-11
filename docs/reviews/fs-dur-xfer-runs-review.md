# Native durable transport runs review

The coordinator read all five modules and compared the frozen port against
FsDurXfer.v sections 0–2d, lines 83–565. Signed block and byte offsets,
ordered left-biased unions, and positional disjointness match the source.
Repeated empty runs remain legal; overlapping nonempty runs preserve the
first payload in the union. These cases are checked by Lean laws.

The fractional argument retains Own, Discarded, and Both, including the
different strict and nonstrict bounds on invalid doubles. It derives mixed
incompatibility from the two invalid doubles. Native byte ownership supplies
disjointness, while source authority supplies byte inclusion. Mixed-run
inclusion needs no disjointness hypothesis. The snapshot agreement instance
uses the existing disk authority.

The independent coordinator audit checked all 89 physical-origin declarations,
their full theorem and opaque bodies, and referenced constructors. It passed
with only propext, Classical.choice, and Quot.sound, zero exclusions, and no
dependency on initial snapshot allocation. The linked build passed 402 jobs.
This prerequisite is approved. Structural footprint correspondence and runtime
source-instance transport remain separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
