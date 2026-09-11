# Independent review: fixed power and observation resources

Reviewer: Codex coordinator, independent of the implementing subagent.
Read the complete PowerGhost modules against pinned `RiscvPtsto.v` generation,
started-counter, observation-half and observation-interpretation definitions.

The generation and start authorities reuse mono-nat slot3 with separate runtime
names. Born, dead and started are raw lower-bound receipts, including the source
successor offsets. They do not use the TSO zero-receipt disjunction. The exact
start count is generation plus the powered-on indicator; monotonicity is proved
for every actual Step constructor. Counter updates use those concrete monotonicity
proofs. A basic update is retained when obtaining the raw zero receipt.

Observation ownership uses native half GhostVar resources. The interpretation
records exact past/future concatenation, actual ObservationsOK, and the machine
half. Silent steps preserve that history through the concrete step invariant;
observed closure requires the already updated machine half and the exact trace
split. Only the joint half update changes ownership. At empty future, the proof
recovers the full trace and its machine invariant. Initial allocation explicitly
requires a real starting trace invariant and returns the client half.

Only slot11 is added, and every prior capacity is preserved. This is fixed
component ownership, not a full era registry, state interpretation or adequacy
proof. The fresh149-declaration audit passed with only the three permitted
standard foundational axioms. Review result: PASS for the declared slice.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
