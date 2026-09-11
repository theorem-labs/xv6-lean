# Durable inode node foundation

Source: `FsNode.v`, `FsStateInode.v:56–365,213`,
`FsStateEra.v:blk_of_seq,node_blk`, and `FsDurSnap.v:119–235` at xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`DurableNode.Node` is the full source record: arbitrary `Dinode`, arbitrary
32-bit indirect-entry list, and concrete finite `ExtTreeMap Nat` of byte
lists. It is distinct from the smaller filesystem-tree `FsNode`. Missing
owned slots read a full zero block. The ownership domain depends on nonzero
addresses and includes allocations beyond file size. Malformed records and
lists are permitted by the carrier; the source representation and validity
conditions remain separate propositions.

`Local` has all sixteen source `inode_local` clauses. `Repr` has the five
source `inode_repr` clauses. `DirLocal` keeps the source's three separate
region conditions, including physical dot positions and orphan cleanliness.
Dots in `Local` retain the nonzero-link guard. The source type enumeration,
32767 link bound, bare-free condition, size/coverage and block lengths are
preserved. The bare-node theorem requires the source's explicit four-way type
condition; it proves the empty directory claim-box case without inventing dots.

The sparse sequence constructor follows the source first-winner recursion.
Its total range lookup law proves the record/entries/data `nodeOf` dictionary
and reconstruction from `Repr`. This helper uses the record's direct addresses
and supplied indirect entries; a separate arbitrary source `blkmap` carrier
and its full `era_node` dictionary remain to be ported. No equivalence for
inconsistent arbitrary record/blkmap pairs is asserted.

Proved source readers include live-file byte lookup, owned-block bounds and
length without a below-size requirement, all bare-node projections, free/claim
local validity, directory-local vacuity, slot injectivity consequences and
empty footprint. Regression theorems check an orphan directory with no entries,
a zero-size inode retaining a nonzero data allocation, and exclusion of slot268
from the data map.

Validation: `python3 tools/lake.py build Xv6.Fs.DurableNodeProofs` passes
14 jobs (proof module 848 ms). The embedded transitive audit checks all 147
public/private durable-node declarations against only `propext`,
`Classical.choice`, and `Quot.sound`.

Next dependencies: source decoded full rounded-region node map and state,
image-to-node local/geometry proofs, bitmap encoding correspondence and the
source link camera with its value choices and root keep-alive slack. The
source `snap_ok`/later boot snapshot and native snapshot resource allocation
are not yet claimed by this node foundation. These modules import no literal
image or generated certificate leaf.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
