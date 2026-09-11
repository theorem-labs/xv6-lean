# Independent review: actual-state TSO interpretation

Reviewer: Codex coordinator, independent of the implementing subagent.
Read all three TsoInterp modules against pinned `RiscvPtsto.v:2099–2141`.

The interpretation has every source conjunct: full timestamp authority, exact
memory domain, per-entry latest-write/pin tie, full log authority and exact list
representation, full monotone log length, complete agent-view authority, and
MemoryOK plus era-image equality. The avf function covers every Nat agent:
actual harts use their views and all other agents use log length. Pointwise domain
equality is explicitly proved equivalent to extensional domain equality.

Boot allocation uses the exact BootFacts empty-log/image/view facts. Timestamp
entries retain every present byte key and have timestamp0 with payNone; the
latest-write proof uses the actual initial memory and empty log. Allocation
returns the adjacent byte authority, full client byte fragments, full client
timestamp fragments and log receipt. No writable byte is converted to persistent
ownership, and no initialized ownership is assumed. The general allocation takes
an explicit finite representation; its finite-address corollary uses encodeAll
only as a logical witness. It does not evaluate the2^64-key enumeration.

The byte component remains explicitly separate from full gen_heap metadata.
No new registry slot is added. Whole-era composition, step ownership preservation,
lifting and adequacy are not asserted. All75 namespace declarations pass the
foundational-axiom audit. Review result: PASS for the declared slice.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
