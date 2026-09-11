# Pure snapshot configuration prerequisites

Frozen bounded port of `iris/FsCfgSnap.v` lines82–131,228–287,297–300,
and756–793 at `arxiv-v1`
(`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). Three modules provide ten
concrete definitions, twenty named public laws, and one private list-union
membership helper.

The decode bridge compares two well-formed records placed at the same
signed block offset. Record-in-block injectivity follows the existing
kernel-checked inode encoder injectivity, with both source record-length
premises retained. `snap_rec_decode` then proves the actual image decoder
returns a named snapshot node's record, under the exact source full-block
and Snapshot.Bytes premises. Region lookup and decode use precisely the
rounded width `ninodes/16+1` and all sixteen records per block.

`defaultNode` is the source `FsNode.fs_node_inhabited` value: scalar fields
zero, EMPTY address list, EMPTY indirect-entry list, and empty block map.
This differs from the well-shaped `DurableNode.zero`; `default_not_zero`
checks that distinction. Total node lookup preserves the fallback on
missing keys. Region definitions match IcacheEscrow.region_inums and
FsCfgBoot.ireg_blk_set, with proved signed interval membership.

The raw node block set contains the address image of every present map
key and the nonzero indirect address. Membership is equivalent to the
existing Node.Owns predicate without Local, a file-size bound, a 268-slot
restriction, or an address-nonzero filter on data-map entries. Thus
malformed and beyond-EOF carriers are preserved. Snapshot.Bytes supplies
the source home-subset and cross-inode disjointness laws. The live-block
union retains arbitrary input inode sets and the total node lookup.

The exact signed free set, bitmap spent set, rounded live inode set, and
whole spent set are concrete finite ExtTreeSets with membership laws.
The spent set includes block1, all log blocks, all inode-region blocks,
bitmap/free-pool blocks, and all live inode blocks. Negative free-pool
sizes yield the empty set. The region metadata proof again names inode
`16*(block-inodestart)` and relies on the rounded region-domain clause.
Finite-map/set enumeration order is immaterial to these proved membership
relations; no raw Rocq container-order equality is asserted.

Validation: `python3 tools/lake.py build
Xv6.Fs.SnapshotConfigBlockProofs` passes 254 jobs. A fresh physical-origin
audit checks all 88 declarations in the three modules, including private
and generated declarations, and every transitive type, opaque/theorem body
(`allowOpaque := true`), and referenced constructor field. Only `propext`,
`Classical.choice`, and `Quot.sound` occur; no unsafe/partial semantic
dependency, zero exclusions. Explicit rejection of
`FsDurSnapshot.Initial` dependencies passes. Working audit:
`/tmp/xv6-lean-research/SnapshotConfigOwnerAudit.lean`.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.

The six inode-region decoding predicates, native bitmap/inode resources,
link routing, inode pool, and configuration allocator remain subsequent
source dependencies. No native configuration allocation is assumed or
claimed by these pure prerequisites.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
