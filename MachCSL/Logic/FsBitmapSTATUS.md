# Native bitmap resource from the snapshot

Frozen bounded port of BitmapInv.bitmap_res/open/timeless (235–250),
FsStateBitmap.free_pool_intro (246–262), and
FsCfgSnap.bitmap_res_of_snap (304–333), at `arxiv-v1`
(`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). Four modules provide six
named laws and the resource's Timeless instance.

The resource is literally the existing freeBitmapAt predicate at the
caller's logged byte view: the full bitmap encoding plus the native pool
of arbitrary full blocks whose used-set bit is clear. It stores no pure
coverage or log-exclusion clause, and its names remain the caller's.
Opening exposes exactly the existing FsBlocks.block and freePool rows.

The generic free-pool introduction converts native finite-set ownership
of every unused block into the source list-shaped pool. A proved finite
set/filter equality and the duplicate-free signed pool sequence supply
the conversion. No block ownership is copied. Arbitrary signed sizes are
accepted, including empty pools for nonpositive sizes, and block zero is
not silently excluded.

The snapshot constructor takes only the source Snapshot.Bytes premise and
the actual bitmapSpent set's FsBlocks.block ownership. It derives the
bitmap byte equation from the restricted-map lookup and derives that the
bitmap block is used from the metadata-used clause. This proves the
bitmap/free-pool sets disjoint, allowing a native separating split. The
pool's byte contents remain existential as in the source. There is no
separate coverage oracle, full-image assumption, or Local premise.

The concrete wrapper selects the existing Disk12 capacity. No ghost
name, camera, or Iris world is allocated, and no physical disk is updated.
The bytes belong to the current logged family, whose relationship to the
physical/logged/durable machine views remains the larger invariant's job.

Validation: `python3 tools/lake.py build MachCSL.Logic.FsBitmapLink`
passes 454 jobs. A fresh physical-origin audit checks all 22 declarations
in the four modules and every transitive type, opaque/theorem body
(`allowOpaque := true`), and referenced constructor field. Only `propext`,
`Classical.choice`, and `Quot.sound` occur; no unsafe/partial semantic
dependency, zero exclusions. Explicit rejection of
`FsDurSnapshot.Initial` dependencies passes. Working audit:
`/tmp/xv6-lean-research/FsBitmapOwnerAudit.lean`.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.

The bitmap invariant, allocation/free updates and instruction proofs,
full inode-region bootstrap, and full filesystem configuration remain
subsequent source dependencies. This slice does not assume a native
allocator or claim that the bitmap invariant has been initialized.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
