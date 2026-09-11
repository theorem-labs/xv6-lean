# Independent review: global register ownership

Reviewer: Codex coordinator, independent of the implementing subagent.
Read the full Defs/Spec/Proofs/Link modules against `RiscvPtsto.v`
`gregs_interp`, `gregs_interp_at`, and both global register accessors.

The native separating conjunction ranges over the complete actual Fin8 set.
Every hart has unconditional membership. The accessor removes exactly one hart
and returns a wand accepting its replacement register file, retaining every
other hart's bridge. Reads and writes use the explicit RegisterSpec; only the
Link imports its implementation. Full initialization inducts over the finite
set, allocates one real register map per hart and updates the explicit name
function. It retains all client cells and does not assume pre-existing names,
name injectivity or a pre-initialized era. A selected cell retains both nested
reassembly wands. Additional Iris frames remain available after a write.

No resource slot is added. The link supplies the proved register contract at its
existing registry capacity. The34-declaration component audit reports only the
standard foundational axioms. Review result: PASS for the declared slice;
whole-machine state interpretation and adequacy remain separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
