# Snapshot image record and block bytes

Frozen bounded source slice: `FsDurImg.v` §11a/b, with the reverse indirect
codec from `FsImg.v:404–463`, at xv6iris `arxiv-v1`
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`SnapshotCodecProofs.lean` proves the missing reverse codec direction.
`leAt_byte` reconstructs each byte of a decoded word with the source's total
zero-default lookup. `encode_decodeDinode_prefix` reconstructs the complete
64-byte record from arbitrary input of length at least 64, ignoring only the
trailing bytes the decoder does not read. `indirectBytes_roundtrip` reconstructs
arbitrary `4*n` bytes from all `n` decoded words. No generated-encoder-input
premise, filesystem validity, file-size bound, or byte-content restriction is
used. The record retains all thirteen address fields.

| Source statement | Lean statement |
| --- | --- |
| `diblk_bytes_split` | `inodeBlockBytes_split` |
| Byte-window reconstruction used by `img_rec_in_blk` | `recordInBlock_decode`, `encode_decodeDinode_prefix` |
| `img_rec_in_blk` | `image_record_in_block` |
| `fs_ind_bytes_round_trip` | `indirectEntries_bytes_roundtrip` |
| `img_node_owns_slot` | `DurableImageNode.image_node_owns_slot` |
| `img_node_fn_naddr` | Existing `DurableImageNode.imageNode_address` |
| `img_node_fn_slot` | `DurableImageNode.image_node_slot_eq` |
| `img_node_slot_inj` | `DurableImageNode.image_node_slot_injective` |
| `img_node_blk_at` | `DurableImageNode.image_node_data_at` |
| `img_node_ind_at` | `DurableImageNode.image_node_indirect_at` |

The record-in-block theorem retains the exact source premise
`0 ≤ i ∧ i < 2^32`, making the unsigned inode cast agree with the signed
index. Superblock inode starts remain arbitrary signed integers. Its proof
splits the actual block using `take`/`drop`; it does not assume encoder
surjectivity or substitute a newly generated record block. All full blocks
have exactly 1024 bytes.

The ownership bridge retains all data slots 0–267 and the indirect-root slot
268. Held data is tied to the actual image using the existing sparse lookup,
independently of inode size or type. A nonzero indirect pointer ties the whole
1024-byte image block to all 256 encoded entries, including entries after EOF.
Neither node representation nor image validity is an extra hypothesis. The
source slot bound is retained in the slot equality API, although the existing
pointwise address equality proves the equality even without that bound.

Validation: `python3 tools/lake.py build Xv6.Fs.SnapshotImageBytesProofs`
passes all 41 jobs; the generic codec module takes about 3 seconds and the
image proof module about 0.5 seconds. A fresh physical-origin audit checks all
**32 declarations** in the two new modules (12 handwritten theorems plus
generated proof helpers) and their complete transitive type/body/constructor
dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` occur; no
unsafe/partial semantic dependency, and zero excluded declarations. Audit
source is retained at
`/tmp/xv6-lean-research/SnapshotImageBytesOwnerAudit.lean` in the working
environment. No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.
Independent review passed; see docs/reviews/fs-snapshot-image-bytes-review.md.

Next source obligations are §11c's used-set and metadata bounds, cross-inode
disjointness and bitmap facts, followed by the home-map coverage ties needed
to construct the full initial `Snapshot.Bytes` and `Snapshot.OK`. This slice
does not claim those results or native snapshot allocation/transport. Frozen
snapshot and filesystem definitions, image bytes, and decoders were unchanged.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
