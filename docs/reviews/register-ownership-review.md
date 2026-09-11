# Independent review: register ownership

Reviewer: Codex coordinator, independent of the implementing subagent.
Read all Register Defs/Spec/Proofs/Link modules and the pinned source
`RiscvPtsto.v` register pointsto, agreement, interpretation and update rules.

The representation uses the actual generated Register keys. The derived order
compares constructor indices and proves injectivity through the generated ofNat
left inverse. No model file was modified. Complete initialization enumerates all
180 constructors; its map lookup theorem holds for every actual Register. Values
are Sigma RegisterType, and typed cells contain the matching key/value pair.
The one-way map/state agreement deliberately permits partial maps, as the source
does. It is carried together with full native GhostMap authority.

The read rule requires both the authoritative interpretation and a matching
fragment; dependent value equality is recovered from Sigma equality. The write
rule requires full cell ownership and updates both the authoritative map and
actual Sail.Registers.write file. Other keys follow the proved write_other rule.
Same-value writes use write_current. Complete-map allocation supplies all client
cells separately, and the cell accessor retains a reassembly wand. Explicit
framing, fraction splitting, agreement and persistence follow native Iris laws.

Slot6 extends the shared six-slot TSO registry. Preserved capacities are derived
at the same indices, with runtime names separate from capacity. The specification
is separate from the proof implementation. No whole-machine interpretation or
adequacy is claimed. A fresh namespace audit checked definitions and private
helpers against the standard foundational axioms:119 declarations passed.

Review result: PASS for the declared register bridge scope.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
