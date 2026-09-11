# Native durable inode readback

Frozen bounded port of `iris/FsDurSnap.v` §7b, lines 933–1111, at
`arxiv-v1` (`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). The four modules
reuse the arbitrary `DurableNode.Node`, its complete stored block map,
the native inode byte predicates, and the four-field `Snapshot.InodeRead`.
There are twelve named laws, including two proved interface structures.

Source mapping:

- `snap_read_blks`, `snap_read_ind`, and `snap_read_pool` correspond to
  lines 942–984. Native fragment/authority agreement reads every stored
  data block, the indirect block when its address is nonzero, and domain
  membership for every unused in-range pool block. Each retains the
  source's explicit full-block premise. No file-size cutoff is added.
- `inode_dat_owns` and `inode_phi_owns` correspond to lines 988–1003.
  Exact `Node.Owns` selects either a present data slot or a nonzero
  indirect root and extracts that separately owned full block.
- `inode_dat_slot_inj` corresponds to lines 1006–1057. It derives
  injectivity on all 269 slots from native separation under the exact
  `PhiExcl` and `DurableNode.Local` premises. It does not assume slot
  injectivity. `data_slots_ne` extracts one entry with `bigSepM_delete`
  before looking up the other; `data_indirect_ne` uses the separate data
  and indirect conjuncts. The same resource is never used twice as two
  linear inputs. The local domain clause supplies data ownership for
  nonzero slots, including allocations beyond end of file.
- `snap_read_inode` corresponds to lines 1061–1092. Under full committed
  blocks, the source's unsigned-32-bit inode range, and local validity,
  it reads the exact four existing `Snapshot.InodeRead` fields. The record
  leg uses the proved wrapped-index/signed-offset bridge and the exact
  64-byte record encoding justified by `Local.record`. The caller's
  superblock and node remain unchanged.
- `snap_read_inodes` corresponds to lines 1094–1111. Pointwise local
  validity and inode-range premises lift the result to every present
  finite-map entry, retaining sparse absence and arbitrary node values.

`dataLeg` and `inodeLeg` only name the source's existing map big-separations;
they add no ownership, new camera, or strengthened carrier. Readers use
only the existing disk camera through `FsDurRead`. There is no allocation,
initial constructor call, or fresh name. `BlocksFull` is not inferred from
`fsSnap` or its pure Shape field.

Validation: `python3 tools/lake.py build
MachCSL.Logic.FsDurInodeReadProofs` passes 416 jobs. A fresh physical-origin
audit checks all 40 declarations in the four modules and their transitive
types, theorem/opaque bodies (`allowOpaque := true`), and referenced
constructor fields. Only `propext`, `Classical.choice`, and `Quot.sound`
occur; no unsafe or partial semantic dependency, zero exclusions. Audit
source in the working environment:
`/tmp/xv6-lean-research/FsDurInodeReadOwnerAudit.lean`.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.

The next separate obligations are cross-inode disjointness, ownership
versus metadata exclusion, and metadata/owned-block used-set coupling.
These are prerequisites for the all-21-field snapshot readback; that
readback, runtime transport, and epoch cloning are not claimed here.

Coordinator full-source review and independent full-body audit passed; see
`docs/reviews/fs-dur-inode-read-review.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
