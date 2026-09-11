# Independent review: reservation ownership

Reviewer: Codex coordinator, independent of the implementing subagent.
Read the complete Defs/Spec/Proofs/Registry/Link modules against pinned
`RiscvPtsto.v:1984–2071`, including the total-map conversion and preserving case.

The concrete finite map has one entry for every actual Fin8 CPU. Unreserved
means a present entry with value None. Reservation values retain the complete
optional ByteMap64 snapshot. The lookup, insertion, all-none and same-value
identities preserve that distinction. Full native GhostMap authority and each
full client cell provide agreement and joint update. The arbitrary-value
existential and framed update retain their source meanings. A preserving write
uses the proved map identity and requires no client cell. Allocation exports all
eight full fragments with access/reassembly, rather than dropping them.

Slot10 extends the device registry and preserves every previous capacity at
its original index. Runtime era names remain explicit; the module adds no
assumption that a current era or machine state has already been initialized.
This is a resource bridge and does not itself establish the machine's reservation
snapshot invariant, which has a separate concrete step proof.

The Link module enforces the standard-three-axiom audit over all113 namespace
and private declarations. Review result: PASS for the declared slice.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
