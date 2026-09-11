# Pure inode-region decoding premises

Frozen bounded port of IcacheBoot's image decoder and six region predicates
(lines286–303 and525–586), FsCfgBoot.image_dinode_fs_dinode (362–392),
and FsCfgSnap.snap_ireg_premises (143–207), at `arxiv-v1`
(`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). The two InodeRegionImage
modules and separate SnapshotRegionProofs module provide eleven definitions
and seven named laws.

The double-list image decoder retains signed Euclidean division/modulo,
Z.to_nat's nonnegative conversion, an empty default block, and the exact
empty-address default record. The slot equation holds under only the
source slot bound. Empty input returns the source default; the additional
negative-one equation checks block0/slot15 behavior outside the guarded
region. No clipping or unsigned cast is introduced in this list reader.

The six predicates are separate source conditions, kept in source order:
free records have zero links; links fit a nonnegative short; types are
0/1/2/3; the supplied count function matches the record's natural link
count; free records are bare; and the supplied record function agrees
with the decoded record. Bare means ONLY size zero plus thirteen zero
addresses. It does not include or imply a type or link-count condition.

The image/list decoder bridge retains every source premise: the outer
list length, sixteen well-formed records per block, pointwise block
encoding, signed in-region index, and the total 32-bit region bound.
It uses the existing actual dinode decoder/encoder theorem with an
explicit checked unsigned cast and slot/block address correspondence.

`snap_ireg_premises` is a separate generic snapshot proof. It takes full
image blocks, Snapshot.Bytes for the restricted map, Local for every
present node, exact rounded width, the 32-bit region bound, the list
length/well-formedness facts, and all block encoding equations. It proves
all six predicates by the checked image/list/node record equality and
each named node's Local facts. No caller premise is dropped or replaced
by a stronger image-wide validity assumption.

Validation: `python3 tools/lake.py build Xv6.Fs.SnapshotRegionProofs`
passes 255 jobs. A fresh physical-origin audit checks all 27 declarations
in these three modules and every transitive type, opaque/theorem body
(`allowOpaque := true`), and referenced constructor field. Only `propext`,
`Classical.choice`, and `Quot.sound` occur; no unsafe/partial semantic
dependency, zero exclusions. Explicit rejection of
`FsDurSnapshot.Initial` dependencies passes. Working audit:
`/tmp/xv6-lean-research/InodeRegionImageOwnerAudit.lean`.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.

These are pure decoding prerequisites. Native inode-region authority,
escrow, bitmap/inode resources, and configuration allocation remain
subsequent source dependencies; no such allocator is assumed here.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
