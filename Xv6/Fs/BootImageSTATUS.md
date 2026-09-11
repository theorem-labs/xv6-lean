# Initial filesystem boot-image contract

Implemented source `FsCfgBoot.v:584–652` and `FsBoot.v:86` at xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`BootImageWF` retains all fifteen premises in source order. Its conjunction
correspondence theorem exposes the exact source formula. Signed superblock
fields, total byte-disk reads and concrete finite `ExtTreeSet Int` coverage
remain unchanged. `CovIn` excludes block zero and checks the whole final byte
of every covered block. Generic theorems derive exact positive coverage below
`sb.size`, the bitmap bound and the exact rounded inode-region endpoint.

The separate `BootImageImage` leaf proves `Image.boot_image_wf` for the actual
checked disk, 2,048,000 bytes, 13 inode blocks and exactly blocks 1–1999. It
reuses the checked W1–W9, rounded-region, parsed-superblock, exact link-count,
free-record and root-self-entry certificates. No image import enters generic
`BootImageDefs` or `BootImageProofs`. Rejection laws cover block zero and a
covered block whose last byte lies beyond the mint.

Validation: `python3 tools/lake.py build Xv6.Fs.BootImageImage` passes. Its
embedded transitive axiom audit permits only `propext`, `Classical.choice`,
and `Quot.sound`.

This is the initial-image premise. `FsCfgBoot.fs_boot_snap_wf` for subsequent
boots requires a committed durable snapshot and its logged-versus-home-byte
ties. The source `snap_ok` includes decoded-node representation, local and
region properties, byte ties, bitmap/ownership/disjointness and the actual
link-family camera validity with root keep-alive slack. That dependency stack
is subsequent work; this initial-image theorem does not assert preservation
of mkfs shape across reboot or establish filesystem resource allocation.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
