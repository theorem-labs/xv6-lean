# Durable inode-node foundation review

Codex coordinator review: PASS. Reviewed all three DurableNode modules against
`FsNode.v`, `FsStateInode.v:56–365`, `FsDurSnap.v:119–235` and the sparse slot
constructor. The carrier retains arbitrary records, indirect-entry lists and
finite slot maps. Representation, all sixteen local clauses, and the three
region directory clauses remain separate propositions with the source guards.

The node reads missing slots as full zero blocks and counts allocations beyond
file size. Bare nodes retain zero links and an empty owned map; orphan directory
claims owe no dot records. Non-orphan directories retain both name-view dots and
the separate physical-position condition. Slot268 is the indirect root and is
excluded from the data map. Reconstruction from the nodeOf helper assumes the
exact representation domain; it does not assert equivalence for an arbitrary
inconsistent external block-map/record pair.

The target build and 147-declaration transitive audit passed. Regression laws
exercise zero-size allocation, orphan-directory emptiness and the top slot bound.
A full durable state, image construction, link-family validity and snapshot
resource allocation remain later obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
