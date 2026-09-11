# Native durable byte readback

Frozen bounded port of the complete `iris/FsDurRead.v` source slice at
`arxiv-v1` (`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). Five modules
provide the exact block-width condition, signed byte-to-block slice
reconstruction, overlap exclusion, free-pool used-bit consequence, and
native snapshot byte/run/block/domain readers. There are 19 named laws,
including the two proved API structures.

Source mapping:

- Lines 54–107: `BlocksFull`, `dblk_full_ok`, `fs_dbytes_block_sub`, and
  `block_of_byte` retain the source's 1024-byte block stride and arbitrary
  signed block keys. No address wrap or unsigned block restriction is added.
- Lines 113–154: `RunSlice` and `run_read` reconstruct the exact stored
  block and prefix/suffix, including the prefix's signed length. Nonempty
  runs, nonnegative offsets, and the original within-block bound remain
  explicit. The pure reconstruction uses extensional list lookup rather
  than adding a codec assumption.
- Lines 166–243: `byte_range_q_overlap`, `blk_run_overlap`,
  `free_pool_used_run`, and `inode_phi_dat` use the actual existing
  `PhiExcl`, `DFrac`, finite pool, and inode byte predicates. The overlap
  condition allows different offsets and values, requires an invalid
  joined fraction, and selects a concrete shared byte. The inode split is
  precisely the already ported record/data/indirect separation.
- Lines 254–260: `FsDurBytes.snapAuth` is reused unchanged, together with
  the native Timeless instance already proved in `FsDurSnapshotProofs`.
  It is an existential authority map contained in the committed flattened
  byte map, not an equality or a full-coverage assertion.
- Lines 270–385: `snap_run_sub`, both run readers, both block readers,
  and `snap_blk_dom` use native `ghost_map_lookup` at the existing disk
  camera. They accept arbitrary source fractions; only the full wrappers
  specialize to `DFrac.own 1`. `ReadSpec` and `OverlapSpec` package proved
  interfaces without new assumptions or cameras.

`RunSlice.full_block` supplies the source reader's final list argument.
`RunSlice.present` and `RunSlice.not_absent` additionally make explicit
that no committed block can be read at an absent map key.

Every block/slice reader retains the source's explicit `BlocksFull D`
premise. The byte-submap reader does not require it. In particular, this
layer does not derive full block lengths from `Pdur`, `fsSnap`, or their
single pure `Snapshot.Shape` condition. It allocates no names or resources
and does not invoke any initial snapshot allocator. Guarded flattening
correspondence is inherited from `FsDurBytes`: full blocks discharge the
length guard, while no malformed overlapping-fold equivalence is claimed.

Validation: `python3 tools/lake.py build
MachCSL.Logic.FsDurReadProofs MachCSL.Logic.FsDurReadOverlapProofs` passes
407 jobs. A fresh physical-origin audit checks all 56 declarations and
all transitive types, theorem/opaque bodies (`allowOpaque := true`), and
referenced constructor fields. Only `propext`, `Classical.choice`, and
`Quot.sound` occur; no unsafe or partial semantic dependency, zero
exclusions. Audit source in the working environment:
`/tmp/xv6-lean-research/FsDurReadOwnerAudit.lean`.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.

Coordinator review approved the full source slice; see
`docs/reviews/fs-dur-read-review.md`. Its independent 56-declaration
full-body audit also passed.

Next obligations are the generic inode readers, ownership-derived
within/across-inode disjointness and used-set coupling in `FsDurSnap` §7b,
then the exact all-field snapshot readback. Source-instance transport and
runtime epoch cloning remain separate; initial pure-input allocation is
not used as a substitute for either.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
