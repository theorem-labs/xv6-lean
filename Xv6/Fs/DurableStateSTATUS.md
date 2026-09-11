# Decoded durable state and image-node bridge

Source: `FsState.v:fs_state_rec,fs_nib,fs_geom`,
`FsCfgBoot.v:img_node,img_nodes,img_inode_local`,
`FsDurImg.v:img_state`, and `FsDurSnap.v:rec_in_blk,snap_meta` at xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`DurableState.State` preserves the parsed superblock, its raw byte list, a
concrete finite map of full durable nodes, and the finite bitmap set. The
carrier has no implicit geometry or validity assumptions. `Geometry` keeps
all four source fields; `Local` quantifies the source sixteen-clause inode
predicate over every stored value. Signed integer arithmetic, including the
rounded `ninodes / 16 + 1`, is unchanged. Metadata includes only the source's
superblock, bitmap and actual stored-inode block roles.

`DurableImageNode.imageNode` uses the actual dinode reader, the exact 32-bit
cast of each indirect entry, and all 268 possible nonzero data-slot addresses.
The cast has a kernel proof that the four-byte decoded integer lies in the
unsigned range; no width conversion is assumed. Its representation theorem
holds for arbitrary block functions. Its total data-reader theorem covers
all natural slots, including the zero default beyond slot267.

The finite image map names all `16 * nib` rounded-region records, including
free records. Exact lookup/inverse/domain laws and an equality to the source
first-winner fold over any enumeration of the same keys justify replacing
stdpp's finite-set enumeration by ascending natural indices. This does not
use the live-only file-tree map. Thirteen blocks give exactly all208 records.

From the full `BootImageWF` premise, the pure bridge proves every image node
`Local` and `DirLocal`, and the resulting state's `Local` and `Geometry`.
The free arm uses both the source bare and zero-link sweeps. The live arm
uses W3, directory validity and physical dots, and the short-link region
bound. Metadata-block separation and record-split bounds are also proved.
All four new Lean modules import only generic definitions/proofs, with no
literal image or generated certificate leaf.

Validation: `python3 tools/lake.py build Xv6.Fs.DurableStateProofs` passes.
An embedded transitive audit checks all durable-node, image-node and state
declarations (including private helpers), allowing only `propext`,
`Classical.choice`, and `Quot.sound`.

Remaining source dependencies before claiming `snap_ok`: the bitmap encoder
and full byte ties, used-block coupling/disjointness, and the actual link
camera's existential value assignment and root keep-alive slack. This stage
proves the decoded state and its local/geometry clauses; it does not claim a
whole snapshot, filesystem resource allocation, preservation across disk
writes, or the later-boot committed/logged-byte contract. The general source
`era_node` on an independently supplied inconsistent `blkmap` remains a
separate dictionary; no equivalence to that arbitrary input is asserted.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
