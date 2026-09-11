# PTE canonicalization independent review

Reviewer: Codex subagent `lean_logic_audit`, independently reviewing the
coordinator's five frozen PteCanonical modules and STATUS. **PASS** for the
declared pure boundary; no code correction requested.

I read the complete pinned `PtAdBits.v`, `PtTree.v:929–1094`, the actual
generated `VmemPte.update_PTE_Bits`, all five Lean files, and the design.
The source pin is `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`setAD` uses the generated nested flag setters and word update. The bit
proof identifies exactly positions 6 and 7, and all other projections
follow from that checked identity. Absorption, reconstruction from the
canonical word, and the actual X/W/R nonleaf classifier are exact. The
extraction lemma retains `lo ≤ hi`, which matters because Sail uses
truncated natural subtraction when forming the result width. The PPN,
extension and low-flag corollaries use the source field ranges.

The byte family preserves the source distinction: interior slots have
eight singleton bytes; leaf slots permit the four A/D choices only at
byte zero. `Leaf` is the source Boolean nonleaf-negation predicate, not a
claim of PTE validity. Byte extensionality reconstructs an exact interior
word or one actual A/D variant. Unconditional canonical read agreement
and leaf-conditioned family preservation therefore require no guessed
validity premise or strengthened visibility condition.

`update_variant` keeps the exact generated `some` equation for arbitrary
access, including cache and prefetch constructors. Its compact proof
abstracts the actual Boolean condition and dirty-bit selection only after
kernel definitional equality identifies the real result expression; it
does not replace an access case or assume a write succeeds. `writeback`
adds the source leaf premise for byte membership. The native Spec has a
proved inhabitant, and the Link corollaries use the same definitions.

This is the specified pure A/D and byte-family dependency, not a claim
that every separately named helper in PtAdBits has its own exported Lean
counterpart. Reservation custody, conditional-write success, KPT tree
ownership, TLB coherence, and real translation remain separate. The
existing model-to-Rocq correspondence limitation is unchanged.

Independent validation rebuilt the Link target successfully (**51 jobs**).
A fresh physical-origin audit checked **91 declarations**, including
private helpers and the complete transitive types, opaque proof bodies
(`allowOpaque := true`) and datatype constructors. It found only
`propext`, `Classical.choice`, and `Quot.sound`, no unsafe or partial
logical dependency, and **zero excluded compiler companions**. Evidence:
`/tmp/xv6-lean-research/PteCanonicalPeerAudit.lean`,
`pte-canonical-peer-audit.log`, and `pte-canonical-peer-build.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
