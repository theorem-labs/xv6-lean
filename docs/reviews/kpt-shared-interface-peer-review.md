# Shared KPT interface and pure proof peer review

Reviewed by the OpenAI Codex Lean-logic subagent, independently of the
coordinator who authored KptSharedPureDefs/PureProofs/Defs/Spec. Result:
PASS for these four modules' interface and implemented pure laws. This is
not a review of the subsequent native invariant proof, which was not yet
implemented at this checkpoint.

I read all four modules, the approved shared-KPT design, the actual
KptOwnership.Capacity/ownership definitions and KptGhost definitions, and
compared KptShare.v:86–150, KptTree.v:331–355 and PtTree.v:1432–1470 at
xv6iris fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.

TreeSpec retains the complete source map: present mappings provide the
exact kernel-permission leaf A/D family and absent mappings require the
source Blocks predicate. snapshot_path transports Maps through canonical
tree agreement while preserving the root and raw upper words. It returns
an existential leaf variant, not the current physical leaf. set_leaf_spec
preserves the full map/absent-map predicate; it derives the source entry
and variant facts by Maps determinism rather than taking them as new
premises. No canonical-invariance law for arbitrary Blocks is assumed.

The invariant body contains exactly the full pinned depth-two tree,
canonical snapshot, bound with log receipt, bare full map authority and
TreeSpec. Capacity.ghost obtains its Views from the same machine capacity,
so publication cannot discharge the bound with an unrelated log camera.
The body has no hart/context index or duplicated full slot.

The four native contracts match the approved boundary: body Timeless;
allocation from already-owned pinned resources, actual log receipt and
both pending shot tokens; masked snapshot extraction; and masked shared
snapshot/map-claim access yielding only a pure snapshot path with three
RAM/alignment facts. Allocation does not require namespace inclusion,
matching source invariant allocation. Access requires ↑N ⊆ E and restores
the same mask. Persistent inputs need not be repeated in the pure result.
read_path does not promise a current word, a successful PTE read, an
all-view receipt, boot publication or TLB coherence. Those remain separate
native event/access layers.

A fresh audit checked all 26 physical-origin declarations across these
four modules, including every type, opaque implementation body with
allowOpaque=true and inductive constructor dependency. Only propext,
Classical.choice and Quot.sound occur; there are no unsafe/partial semantic
dependencies and zero exclusions. Evidence is recorded outside the repo in
KptSharedInterfacePeerAudit.lean and kpt-shared-interface-peer-audit.log.
No production source changes or contract corrections were requested.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
