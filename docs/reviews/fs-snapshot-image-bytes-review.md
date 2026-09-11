# Snapshot image-byte independent review

Reviewed the frozen `Xv6/Fs/SnapshotCodecProofs.lean` and
`SnapshotImageBytesProofs.lean`, their status, and the relevant existing
codecs, record-in-block predicate, image-node decoder and slot definitions.
Compared against pinned `FsDurImg.v` §11a/b (`1079–1293`) and
`FsImg.v:404–463` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
Result: pass; no correction required for the declared slice.

The reverse record codec starts from arbitrary bytes of length at least 64.
It proves equality to the complete 64-byte prefix, rather than assuming that
the bytes came from `dinodeBytes`. The first twelve bytes cover four 16-bit
fields and the 32-bit size; the remaining 52 bytes cover all thirteen
32-bit addresses. The decoder's structural well-formedness supplies only
the address-list length, with no hidden filesystem validity assumption.
Trailing bytes are ignored exactly because the decoder does not read them.
The per-word lemma also retains the existing total zero-default byte lookup.

The indirect reverse codec reconstructs all `4*n` arbitrary bytes and is
instantiated at 256 entries for a complete 1024-byte block. It includes
entries after EOF and imposes no live-inode, type, file-size or byte-content
condition. The nonzero indirect-pointer premise is retained, preventing
the zero-pointer decoder's synthetic zeros from being equated to an
arbitrary image block.

`inodeBlockBytes_split` matches the source's arbitrary-list theorem with
per-record structural well-formedness and an in-range index. The image
record proof uses direct `take`/`drop` reconstruction to establish the same
split-shaped `RecordInBlock` predicate; it does not assume encoder
surjectivity. I checked the explicit `0 ≤ i ∧ i < 2^32` premise and cast
proof: they justify replacing the unsigned inode number with the signed
source index in both block division and slot remainder. Superblock inode
starts remain arbitrary signed integers. The source 1024-byte block size
and 64-byte record size provide room for every one of the sixteen slots.

The ownership translation covers every data slot 0–267 and the separate
indirect-root slot 268, for 269 source slots in total. The source `k ≤ 268`
bound remains in the slot-equality API even though the underlying pointwise
address lemma proves more. Slot injectivity transfers the exact nonzero
premise and equality. A held data block is tied to its actual image bytes
through the sparse node lookup, while a held indirect root is tied to the
entire reverse-coded block. No node representation, image validity, or
live-inode premise is silently added. These results consequently apply to
free records and rounded inode-region entries whenever their stated
premises hold; this slice does not filter the region to live inodes.

Independent validation:

- `python3 tools/lake.py build Xv6.Fs.SnapshotImageBytesProofs`: passed
  41 jobs.
- `python3 tools/lake.py env lean /tmp/xv6-lean-research/SnapshotImageBytesIndependentAudit.lean`:
  enumerated all 32 physically originating declarations, including generated
  helpers, and traversed their full statement/proof dependencies. Only
  `propext`, `Classical.choice`, and `Quot.sound` occur; no unsafe or partial
  semantic dependency and no runtime-companion exclusion occurred. The
  printed record reverse-codec and image-record roots use only `propext`
  and `Quot.sound`.

The component does not yet prove §11c's used-set coupling, metadata bounds,
cross-inode disjointness, home-map coverage, complete snapshot validity, or
native snapshot allocation/transport. Its status states these limits
accurately. This is an independent source review of the new codec layer;
it does not claim a mechanized cross-prover equivalence proof or an
independent reimplementation of the pre-existing image decoder.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
