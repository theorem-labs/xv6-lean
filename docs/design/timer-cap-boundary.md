# Per-hart timer resource

The full source TimerCap.v (113 lines) was read at the pinned paper commit.
The native definition retains the actual per-hart mcounteren value at a
discarded fraction with TM=1, and the full stimecmp cell at an existential
value inside the exact source timer namespace invariant. Both resources use
the supplied machine register capacity and current era's same CPU name.

Four contracts construct the deadline assertion, freeze actual supplied
counter-enable ownership, allocate the combined persistent capability from
both actual register cells, and derive TM=1 for another held description
of that same counter-enable register by native agreement. No current
deadline meaning, timerinit execution, STCE configuration or successful CSR
instruction is inferred from these resource constructors. No new camera
or register authority is allocated; only the source deadline invariant is
installed. This capability is a prerequisite of the full supervisor bundle.

The independently approved signatures are implemented natively in four modules
(352 build jobs). The full 27-declaration owner audit passed with only the
standard three axioms and no exclusions. Complete independent implementation review passed
(27 declarations); see docs/reviews/timer-cap-peer-review.md. Native CSR rules, boot reachability and per-hart delivery through
migration remain later obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
