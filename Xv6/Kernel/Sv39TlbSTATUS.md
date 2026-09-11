# Native Sv39 level-zero TLB fill and lookup

The four modules Defs, Spec, Proofs and Link discharge all six contracts
against the actual pinned generated `add_to_TLB`, `lookup_TLB` and
`match_TLB_Entry` programs. They prove the actual hash is below 64,
replacement at exactly that index, preservation at every other index,
and subsequent lookup of the inserted entry.

The entry retains the actual ASID, arbitrary global bit, signed VPN,
zero level mask, PPN, raw PTE and originating physical PTE address.
The register plan preserves the generated fill's read/write/read callback
sequence and lookup's read. It owns the single actual TLB register and
works for every old 64-entry vector and every supplied raw word.

This is an algebraic and native register-program result. It does not
assert that arbitrary PTEs are valid, establish shared page-table
ownership, or prove coherence of other cached entries. Composition with
the physical Sv39 walk and A/D update is a separate translation-miss
proof; TLB-hit coherence and the complete translation front end remain open.

Validation: the 427-job build passed. Root and independent peer audits
each checked all 33 declarations, including types, opaque bodies and
constructors, with zero exclusions and only the three standard Lean
foundational axioms. The independent report is
`docs/reviews/sv39-tlb-peer-review.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
