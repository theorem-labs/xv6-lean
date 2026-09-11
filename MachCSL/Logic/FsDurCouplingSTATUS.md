# Native durable ownership coupling

Frozen bounded port of `iris/FsDurSnap.v` §7b, lines 1115–1258, at
`arxiv-v1` (`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). Four modules
provide the source's five coupling propositions and their proved interface.
They reuse the arbitrary inode/state carriers, exact `Node.Owns`, signed
metadata addresses, and existing finite native ownership predicates.

Source mapping:

- `fs_inodes_phi_disj` reads cross-inode block disjointness from native
  separation under `PhiExcl`. For distinct inodes, it deletes the first
  entry before looking up the second; shared block addresses contradict
  separately owned full bytes. It assumes no pure disjointness or local
  inode property.
- `fs_inodes_phi_used` proves that an inode-owned block in the stated
  signed pool bounds belongs to the used set. The proof extracts the
  inode's actual data/indirect block and applies the existing free-pool
  exclusion law. It adds no global validity assumption.
- `inodes_owns_and_rec` extracts one inode's block together with another
  inode's record. When the indices coincide, it splits the record and
  data/indirect conjuncts of the same entry. When they differ, it deletes
  the selected entry before the second lookup. No ownership is duplicated.
- `fs_owns_not_meta` refutes overlap with each exact metadata arm:
  superblock, bitmap, or a present inode's record block. The record arm
  uses the unsigned-32-bit index bound and local record well-formedness
  to obtain its exact 64-byte run. This works for the same inode too.
- `fs_meta_used` proves metadata membership in the used set under the
  original block-range premise. Superblock and bitmap use full-block
  exclusion; record regions use the source's nonempty-run exclusion.

`metadataLeg` merely groups superblock, bitmap, and inode-map byte legs in
source order. It contains no geometry, local validity, block-width oracle,
or additional ownership. The two metadata theorems retain the exact
pointwise inode-range and `DurableNode.Local` premises. Neither theorem
assumes `Snapshot.OK`, metadata separation, or already checked used bits.
No allocation, new ghost name, camera, or source carrier is introduced.

Validation: `python3 tools/lake.py build
MachCSL.Logic.FsDurCouplingMetadataProofs` passes 415 jobs. The six named
laws include the proved `CouplingSpec`. A fresh physical-origin audit
checks all 24 declarations and their transitive types, theorem/opaque
bodies (`allowOpaque := true`), and referenced constructor fields. Only
`propext`, `Classical.choice`, and `Quot.sound` occur; no unsafe or partial
semantic dependency, zero exclusions. Audit source in the working
environment: `/tmp/xv6-lean-research/FsDurCouplingOwnerAudit.lean`.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.

The next separate obligation is the complete `fs_snap_read_ok` assembly:
all 21 snapshot byte fields and per-inode local validity must be read from
the existing native resources with the source's external full-block
premise. Runtime epoch transport and cloning remain separate obligations.

Coordinator full-source review and independent full-body audit passed; see
`docs/reviews/fs-dur-coupling-review.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
