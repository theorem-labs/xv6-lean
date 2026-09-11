# Full initial filesystem snapshot

`SnapshotImageProofs.lean` proves the complete pure theorem corresponding to
`FsDurImg.img_snap_ok` (§11d, source lines 1382–1652) at xv6iris `arxiv-v1`
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. Its sole hypothesis is the existing
**fifteen-conjunct `BootImageWF`**. No byte, inode, bitmap, native-camera,
coverage, or ownership fact is added as a separate assumption.

`image_bytes` constructs every field of the unchanged `Snapshot.Bytes`:

| Field | Proof input |
| --- | --- |
| `blockSize` | Exact home restriction lookup and block reader length |
| `superblock` | Covered superblock outside the log |
| `parse` | Existing boot-image parser equality |
| `bitmap` | Full bitmap byte roundtrip, including padding bits |
| `pool` | W5 free-block range and actual home coverage |
| `inum` | Complete rounded inode region and 32-bit bound |
| `repr` | Actual decoded image-node representation |
| `record` | Full 64-byte reverse codec at the signed inode-block address |
| `data` | Held-slot bytes, live-inode ownership, and home membership |
| `indirect` | Full 256-entry/1024-byte roundtrip and home membership |
| `domain` | All advertised inodes are present |
| `links` | Explicit image choice, `ElemOK`, and proved native-camera validity with the extra root token |
| `metadataUsed` | Source metadata bounds and W5 bitmap membership |
| `ownedUsed` | Owned blocks are bitmap-used and not metadata |
| `disjoint` | W4 duplicate freedom across distinct live inode lists |
| `superblockOK` | Source W1 |
| `region` | Exact rounded inode-block geometry |
| `slot` | W4 live-inode injectivity and vacuous bare-node injectivity |
| `regionDomain` | Every rounded-region inode remains present |
| `directory` | All three existing source directory-local clauses |
| `domainBelow` | Actual home coverage and the disk-byte bound |

`image_snap_ok` pairs these bytes with the existing `imageState_local` theorem,
giving the exact conjunction `Snapshot.OK`. `image_snap_holds` supplies the
same concrete state as the existential witness. The state retains the actual
superblock block, all rounded-region records (including free records), all
held data/indirect blocks, and the complete bitmap set. The disk map is exactly
the original block image restricted to the covered home set; all 31 log blocks
are excluded by that already defined set operation.

`SnapshotImage.lean` is the separate literal-image leaf. `Image.snapshot_ok`
and `Image.snapshot_holds` instantiate the generic result with the already
checked initial image: the 2,048,000-byte filesystem, thirteen inode blocks
and all 208 rounded-region records, and its existing `initialCoverage`.
The leaf reuses `Image.boot_image_wf`; it does not regenerate image bytes or
replace a source equality with a host assertion. Generic proof imports remain
free of literal image dependencies.

Validation: the generic target passes 264 jobs (new module about 0.8 seconds),
and `python3 tools/lake.py build Xv6.Fs.SnapshotImage` passes 484 jobs (leaf
about 0.8 seconds). The leaf enforces the foundational axiom allowlist for
both concrete results. A fresh physical-origin audit checks all **16
declarations** from these two modules (five public theorems and generated
proof helpers), following all transitive types, bodies, and referenced
constructor fields. Only `propext`, `Classical.choice`, and `Quot.sound`
occur; no unsafe/partial semantic dependency and zero excluded declarations.
The audit source is retained at
`/tmp/xv6-lean-research/SnapshotImageOwnerAudit.lean` in the working environment.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used. Independent review passed; see docs/reviews/fs-snapshot-image-review.md.

One generic declaration locally raises elaboration recursion depth to 2048.
The concrete leaf locally marks the existing state/map builders irreducible
for theorem matching. These proof elaboration settings change no definition,
byte, premise, kernel equality, or runtime behavior.

This closes the full **pure initial `snap_ok` obligation**. The next source
dependency is native durable filesystem resource allocation (`FsDurAlloc` and
`FsDurSnap.P_dur_alloc`) and the source epoch/transport interface. Those native
resources, crash/reboot preservation, kernel initialization, and whole-system
adequacy are not conclusions of this pure theorem. Frozen definitions and
previously reviewed proof modules were unchanged.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
