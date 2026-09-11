# Native inode-slot reference and mirror coupling review

Coordinator review: pass for all five IcacheSlotCoupling modules. All pure and
native definitions, specifications, proofs and links were read against the
pinned InodeRegion.v fresh/claim/reference/freeze predicates and the native
rcol/frzc definitions and movers (435–450, 555–587, 671–994, 1746–1779,
1955–2085).

The pure predicates retain both reference flavors, the exact thirteen zero
addresses of a fresh record, typed claim information, raw invalid/absent
exclusive branches, and the distinct pre/count-one versus post/count-zero
freeze conditions. They impose precisely their source record-type/link-count
constraints. Native rcol owns the actual per-key ledger authority with its
existential licensed count; frzc owns an actual half mirror with its equation.
No record ownership or transaction share is inferred from these pure clauses.

Mint/spend retain the source flavor conditions and derive positive counts from
the held native fragment. Paired count updates require both real count halves,
first establish equality by camera agreement, and then update both halves and
the ledger at their existing names. The boot theorem only regroups supplied
finite rows: both count halves, both mirror halves and the off-freeze fragment
survive. Its arbitrary record function is sound because zero-reference and
off-freeze predicates do not constrain those records. It allocates nothing.

The independent fresh audit checked all 102 declarations, full types, opaque
bodies and constructors, rejecting unsafe/partial dependencies and native
initializers. Only the standard three axioms occur, with zero excluded roots.
Evidence: IcacheSlotCouplingOwnerAudit.lean and icache-slot-coupling-peer-audit.log
under /tmp/xv6-lean-research.

The full inode slot still needs record and top custody, claim/freeze transaction
pins, epoch receipts, boot shelter, escrow tickets and checked-out arms. These
coupling lemmas do not claim those unimplemented resources.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
