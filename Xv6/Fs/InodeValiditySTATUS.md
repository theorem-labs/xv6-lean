# Inode validity and full-region checks

This slice follows `iris/FsImg.v` at xv6iris `arxiv-v1`, commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. It ports the W3 image-validity
conditions and the separate rounded inode-region checks. It does not substitute
the later durable-filesystem DWF conditions.

| Source | Lean |
| --- | --- |
| `fs_nblk`, `fs_nblocks`, cover/max/index bounds (684–751) | `nblk`, `nblocks`, `nblk_cover`, `nblocks_cover_nat`, `nblk_max`, `nblk_lt` |
| `fs_addr_ok`, `fs_inode_wf`, nine-field `fs_inode_ok` (962–1024) | `addrValid`, `inodeValid`, `InodeOK` |
| `fs_inode_wf_ok`, `fs_inode_ok_blk` | `inodeValid_iff` (both directions), `inodeValid_ok`, `InodeOK.block` |
| `fs_inodes_wf/spec` | `inodesValid`, `inodesValid_spec` |
| `fs_region_free/spec` | `regionFree`, `regionFree_spec` |
| `fs_region_nlink`, L3/L4 projections | `regionNlink`, `regionNlink_free`, `regionNlink_short` |
| `fs_rec_bare`, `fs_region_bare`, size/address projections | `recordBare`, `regionBare`, `regionBare_size`, `regionBare_addr` |
| `fs_region_wf/free/nlink` | `regionValid`, `regionValid_free`, `regionValid_nlink` |
| `fs_live_set/elem_of` | `liveInodes`, finite `liveSet`, `liveInodes_mem`, `liveSet_mem` |

The existing `dinode`, `indirectEntries`, `blockAddress`, and `dataOf` readers are
reused. Inode indices still wrap modulo32 bits before block/slot selection;
arbitrary superblock fields stay signed integers. Byte and address-list lookups
retain their source zero defaults. Arbitrary Dinode address-list lengths are
preserved; a decoder's13-entry guarantee is separate from W3.

W3 retains all nine source obligations: one of the three live types, a positive
link count, the268-block size cap, in-range used direct addresses, zero unused
direct addresses, absent or valid indirect block, in-range used indirect entries,
and zero unused indirect entries. A type-zero inode is skipped by the whole-inode
W3 sweep. The region nlink and bare checks are necessary separate conditions.
`regionValid` combines only tail-freedom and link-count checks; `regionBare` is
not folded into that source bundle.

All region predicates sweep16*nib records, rather than stopping at ninodes.
`region_classify` combines W3 with the tail check to classify every record in the
rounded region. `liveSet` is a concrete finite `Std.ExtTreeSet Int`; its membership
law exactly matches the source's `list_to_set` of live integer inode numbers.
Negative inode counts enumerate an empty list exactly as source Z.to_nat does;
these checks alone do not imply valid superblock geometry.

The bare-record address theorem applies at every Nat index, strengthening the
source's k<13 statement without a new assumption: present addresses are checked
by the whole-list `all`, and missing addresses have the existing zero default.
`dinode_type_blocks` proves a type-only disk-read normalization, retaining signed
block addresses and modulo32 inode indexing. It avoids materializing irrelevant
1024-byte blocks in concrete leaf proofs.

Pure modules import no actual image. `InodeImage.lean` is a separate concrete
leaf and proves:

- The exact pinned initial image has live inodes1–22, with a finite-set membership
  theorem. The source comment claiming1–24 is stale: the kernel rejected that
  candidate equality, and both the raw image bytes and the source reader yield22.
- The13-block region contains208 inode records, and all eight tail records200–207
  are type zero.

These leaf results do not assert that every initial live inode satisfies W3.
The separate `InodeCertificates.lean` now checks the full initial region
nlink/bare predicates and the combined region validity; full initial W3 remains
separate work. The abstract implication and coverage theorems
are complete for this slice. Block uniqueness, bitmap ownership, directory/tree
validity, full fsimg_wf, boot resource allocation and crash consistency remain
separate later obligations.

Validation:

```sh
python3 tools/lake.py build Xv6.Fs.InodeImage
```

`InodeValidityProofs` enforces an audit over every imported filesystem theorem
and its private helpers, allowing only propext, Classical.choice and Quot.sound.
The concrete leaf enforces the same audit for all four image theorems. Kernel
regression facts check rejection of nonzero unused direct addresses, negative
count/empty-region behavior, and the important distinction that W3 skips a free
record with garbage fields while the separate nlink/bare checks reject it.
No native evaluator, custom axiom or placeholder participates in these proofs.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
