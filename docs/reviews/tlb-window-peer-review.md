# Independent two-tree TLB window review

PASS. I am the Codex lean_logic_audit peer reviewer, separate from the
coordinator who authored TlbWindow. I read all four Defs/Spec/Proofs/Link
modules and the complete pinned source PtTree.v:1999–2112. No correction
is required and no implementation or frozen TlbCoherence file was changed.

Coherent puts the previous/current disjunction inside the quantification
for each occupied hash slot, exactly as source tlb_ok_pt2. It permits mixed
provenance within the same 64-entry vector. It neither chooses one tree
for the entire vector nor equates an entry's installing root with a later
active root. Each branch retains TlbCoherence.CacheOf, including origin
VPN with equal hash, stored ASID, raw global bits, level mask, PPN, installing
leaf-slot address and arbitrary stale A/D bits.

The seven source laws map directly to previous, canon_current,
canon_previous, fill_current, fill_previous, set_leaf_previous and
set_leaf_current. The additional current injection, swap and collapse
follow pointwise propositional reasoning. They do not erase mixed
provenance unless the two trees are explicitly equal in collapse.

Fill handles equal hash rather than equal VPN. The selected index receives
the exact existing generated level-zero entry and the matching side's Maps
witness; every different hash keeps its original per-entry disjunction.
The previous-side proof derives the symmetric law without rewriting the
entry's origin address. Both sides accept an arbitrary A/D Variant of the
mapped leaf and preserve raw upper G/RSW behavior through the shared entry
definition. No hash injectivity or noncollision premise is introduced.

Canonical transport changes only the selected side. The two set-leaf
proofs use the proved canonical-tree update identity and native single-tree
cache transport. Their omission of the source's redundant updated-leaf
validity/leaf/NAPOT/PBMT premises is justified by the existing Maps and
A/D-stability proofs in that dependency. This is not a claim that arbitrary
invalid nonleaf words preserve their classification under canonicalization.
Link constructs Spec with TlbCoherence.nativeSpec; no caller-supplied
coherence implementation remains.

These are pure provenance laws. The modules do not claim an operational
SATP write, sfence sequence, hit refresh, native WP, or completed switch
protocol. Future operational integration must still associate the
previous/current trees with the actual hardware and invoke the appropriate
per-entry branch. No source/Lean cross-backend equivalence is asserted.
Source pin: fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.

Independent validation: target build passed 453 jobs. The fresh
physical-origin audit checked all 29 declarations in four modules,
including private declarations, types, opaque bodies and constructor
fields. Only propext, Classical.choice and Quot.sound occur; no
unsafe/partial dependency, zero exclusions. All four source SHA256 hashes
were unchanged through review/build/audit. Local evidence is
/tmp/xv6-lean-research/TlbWindowPeerAudit.lean,
tlb-window-peer-build.log, tlb-window-peer-audit.log and
tlb-window-peer-before.sha256.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
