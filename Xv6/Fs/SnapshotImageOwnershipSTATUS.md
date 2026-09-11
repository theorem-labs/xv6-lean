# Snapshot image ownership and coverage

Frozen source slice: `FsDurImg.v` §11c and the ownership/coverage helper
proofs inside §11d, at xv6iris `arxiv-v1`
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`SnapshotImageOwnershipProofs.lean` provides ten pure theorems:

| Source obligation | Lean statement |
| --- | --- |
| `img_owned_block` | `image_owned_block` |
| `img_used_of_blocks` | `image_used_of_blocks` |
| `fs_inode_blocks_disjoint` used by `sk_disj` | `inodeBlocks_disjoint` |
| `Hlive_of_owns` | `image_owns_live` |
| `Hownhome`, with rounded-region lookup retained | `image_owned_home` |
| `Hmeta_below` | `image_metadata_below` |
| `sk_own_used` helper | `image_owned_used` |
| `sk_disj` helper | `image_owned_disjoint` |
| `sk_slot` live/bare split | `image_slot_injective` |
| `sk_pool` free-block coverage | `image_pool_home` |

The first theorem retains exactly image validity, advertised inode bounds,
nonzero inode type, and ownership. It translates the complete 269-slot view
into the source's ordered `inodeBlocks` using the already proved W3 equality
with nonzero slot entries. W3 then supplies the block bounds. The generic
distinct-inode lemma uses only duplicate freedom of the source `usedBlocks`
list and the source bounds/live/distinct-index premises; no bitmap or set
disjointness assumption replaces W4.

The bitmap bridge retains the source bound `0 ≤ b < size` and the exact
metadata-or-used-block disjunction. It uses W5 and the superblock's one-bitmap
bound to conclude membership in the actual decoded bitmap set. Bits beyond
`size` remain unconstrained by W5; their byte representation is unchanged.

The boot helpers take the existing fifteen-conjunct `BootImageWF` contract.
They preserve every inode in the rounded region, including free records.
The bare and region-free checks prove that a node owning a block must be a
live advertised inode; free nodes are never silently removed. Coverage is
derived from the actual home-set exclusion of all 31 log blocks. Metadata
uses the actual stored-inode domain, and block addresses remain signed.

The source free pool begins at block zero. W5 marks zero as metadata-used,
so a free-pool member must lie in the data range and the covered home map.
No positivity premise was added to the pool predicate or disk carrier.

Validation: `python3 tools/lake.py build
Xv6.Fs.SnapshotImageOwnershipProofs` passes all 46 jobs, with the new module
taking about 0.6 seconds. A fresh physical-origin audit checks all **22
declarations** (ten handwritten theorems and generated proof helpers), their
transitive types and bodies, and referenced constructor fields. Only
`propext`, `Classical.choice`, and `Quot.sound` occur; no unsafe/partial
semantic dependency and zero excluded declarations. The audit source is
retained at `/tmp/xv6-lean-research/SnapshotImageOwnershipOwnerAudit.lean` in
the working environment. No `sorry`, custom axiom, `native_decide`, or
`bv_decide` is used. Independent review passed; see docs/reviews/fs-snapshot-image-ownership-review.md.

Next: assemble all 21 `Snapshot.Bytes` fields, pair them with the existing
local-node interpretation to prove `Snapshot.OK`, and instantiate the
generic theorem with the already checked concrete image contract. This
checkpoint does not claim that assembly or native snapshot resource
allocation/transport. Frozen filesystem, snapshot, byte, and ownership
definitions were unchanged.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
