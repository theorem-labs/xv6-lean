# Independent durable state and decoded image review

Result: **PASS for the declared partial scope.** No source correction was required. This review covers `Xv6/Fs/DurableNode{Defs,Spec,Proofs}.lean`, `DurableState{Defs,Proofs}.lean`, `DurableImageNode{Defs,Proofs}.lean`, and their status records. The reviewer did not implement this slice and did not edit its source files.

The reference is the paper artifact `.upstream/xv6iris` at `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The review compared executable definitions and proposition fields, including the supporting `FsCfgBoot.v`, `FsImgBridge.v`, `FsStateEra.v`, `FsDurSnap.v`, and `DirView.v` definitions, rather than relying on source comments alone.

## Source correspondence

| Source | Lean counterpart and finding |
| --- | --- |
| `FsNode.v` node record; `FsStateInode.v` readers and local conditions | `DurableNode.Node` retains arbitrary records, indirect-entry lists, and finite block maps. `Repr`, `Local`, and `DirLocal` are separate propositions; validity is not imposed by the carrier. |
| `FsDurSnap.v:204` `inode_repr`; `FsStateInode.v:119` `inode_local` | All five representation conditions and all sixteen local conditions are retained. In particular, allocated blocks beyond file size are permitted, all stored blocks must have length 1024 under `Local`, and free inodes must be bare. |
| `DirView.v:855`, `:963`, `:1049`, `:1055`; `FsStateInode.v:213` | Directory inode bounds, physical dot positions, and orphan cleanliness remain distinct. The nonzero-link guards on the ordinary dot obligations are preserved; orphan directories have the separate dots-only condition. |
| `FsState.v:63`, `:106`, `:109` | `DurableState.State`, `State.nib`, and `Geometry` preserve the four-field state and all four geometry conditions. Signed superblock arithmetic remains signed until the source natural-number conversion. |
| `FsDurSnap.v:104`, `:175` | `RecordInBlock` is the exact prefix/serialized-record/suffix relation, with signed offset equal to prefix length. Its size consequence explicitly requires record well-formedness. `Metadata` includes block 1, the bitmap block, and blocks containing stored inode keys. |
| `FsCfgBoot.v:105`, `:109`; `FsImgBridge.v:76`; `FsStateEra.v:135`, `:178`, `:202` | `imageNode` specializes the source decoder to its consistently derived record, indirect entries, and address map. The tail-first finite-map construction and all 268 possible data slots agree with the source construction. |
| `FsCfgBoot.v:127–286` | `imageNode_bare`, `imageNode_local_free`, `imageNode_local_live`, `imageNode_local`, and `imageNode_dirLocal` establish the corresponding initial-image consequences with their stated `BootImageWF` premises. |
| `FsDurImg.v:148` | `imageState` uses the supplied superblock, actual superblock block, full decoded inode map, and bitmap decoded from the bitmap block. It retains all 8192 bitmap bits; it does not impose an invented tail-bit condition. |

## Critical checks

The inode map covers exactly `0 ≤ i ∧ i < 16 * nib`. It does not filter on the inode type or advertised inode count. `imageNodes_keeps_free` makes free-record retention explicit, and `thirteen_blocks_domain` gives the full 208-record domain for thirteen inode blocks. The generic local proof handles the padded tail using the source region-free condition, then uses the free-inode proof; it does not silently discard those records.

`imageNodes_source_map` proves equality with a map built from **any** source key enumeration whose membership is that full region. Duplicates are harmless because every occurrence of a key carries the same decoded node. This establishes enumeration independence without assuming that the Lean recursion has the same ordering as `stdpp.elements`.

The indirect-entry cast has a checked arithmetic bridge. The proof derives the unsigned 32-bit bound from the four-byte little-endian reader before casting to `BitVec 32`, including total zero-default reads and out-of-range list lookup. `imageNode_address` proves the resulting address equality for every natural index; `imageNode_data_all` also handles indices beyond the 268-slot region. These are mathematical reader equalities, not an assumed equivalence between proof assistants.

`imageState_local` and `imageState_geometry` establish all stored-node local conditions and all four geometry fields from the packaged initial-image assumptions. In particular, complete rounded-region presence and directory locality are actually proved. Neither theorem turns the unrestricted state carrier into a validity subtype.

## Validation and limits

Independent commands on 2026-09-11:

```text
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Fs.DurableStateProofs
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/DurableStateIndependentAudit.lean
```

The build passed all 34 jobs. The fresh audit traversed the axiom dependencies of all 264 declarations in the three public namespaces and their private durable-module namespaces. Every dependency was within `propext`, `Classical.choice`, and `Quot.sound`. A recursive inspection of the local import closure found no generated image constants or concrete image certificate leaf imports.

This is a faithful generic initial-image/state slice. It does not yet port arbitrary inconsistent `era_node` record/block-map inputs, snapshot byte equalities, the full bitmap encoder and ownership correspondence, used-set coupling, allocation/disjointness resources, link-camera assignments, snapshot allocation, or preservation under disk writes. It proves neither `snap_ok` nor the later boot contract. The status records make those boundaries explicit. No additional omission or strengthening was found within the claimed scope.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
