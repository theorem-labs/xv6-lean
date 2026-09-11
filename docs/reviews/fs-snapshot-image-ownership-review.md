# Snapshot image ownership independent review

Reviewed frozen `Xv6/Fs/SnapshotImageOwnershipProofs.lean` and its status,
against pinned `FsDurImg.v` §11c and the relevant ownership/coverage helpers
of §11d (`1291–1625`), together with `FsImg.fs_inode_blocks_disjoint` and
the called Lean W3/W4/W5, bare-region, and home-set lemmas. Source pin:
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
Result: pass; no correction required for this ten-theorem slice.

`image_owned_block` retains image validity, advertised inode bounds,
nonzero type, and actual node ownership. Its route through nonzero slot
entries uses the proved W3 equality to the source's ordered `inodeBlocks`,
then its exact block-range theorem. This covers both data slots and the
indirect root without assuming their conclusion as an input.

`inodeBlocks_disjoint` consumes duplicate freedom of the actual flattened
`usedBlocks` list. Its lookup proof selects the two distinct bounded live
inode chunks and applies the proved cross-chunk consequence of list
`Nodup`. The final `image_owned_disjoint` obtains that premise from W4.
Neither theorem substitutes a new set-disjointness assumption, a modified
collector, or an ownership-domain axiom. The single-inode slot-injectivity
proof likewise derives its live case from the same W4 and W3 checks.

The bitmap bridge retains precisely the source bounded block premise and
metadata-or-used-list disjunction. W5 and the one-bitmap size bound supply
membership in the decoded bitmap. Bits after the advertised filesystem
size remain untouched and unconstrained by that checker.

Every rounded-region record remains in the image node map. In
`image_owns_live`, the existing bare check and region nlink condition make a
free record's ownership empty; the region-free condition excludes live
records beyond the advertised inode count. The free branch of slot
injectivity is proved from the same bare node, rather than by removing it.
These helpers take the unchanged fifteen-conjunct `BootImageWF` contract.

Home membership follows the existing coverage clauses and exact exclusion
of the log header plus thirty log-data blocks. The metadata bound uses the
actual stored-inode domain and the rounded-region equation, leaving signed
addresses and the general disk carrier unchanged. `image_pool_home` starts
from `0 ≤ b < size`, including zero: W5 forces every such free block into
the data range. No positive-block premise is added to the free pool and
`CovIn` is not weakened to admit zero. The general home-set operation also
retains its existing signed semantics; positivity comes from the explicit
boot coverage contract where required.

Independent validation:

- `python3 tools/lake.py build Xv6.Fs.SnapshotImageOwnershipProofs`: passed
  46 jobs.
- `python3 tools/lake.py env lean /tmp/xv6-lean-research/SnapshotImageOwnershipIndependentAudit.lean`:
  checked all 22 physically originating declarations and recursively
  traversed their complete type/proof dependency cones. Only `propext`,
  `Classical.choice`, and `Quot.sound` occur. No unsafe or partial semantic
  dependency occurred; no runtime companion was excluded.

The ten statements are helpers for the final snapshot assembly. This review
does not assert that all 21 `Snapshot.Bytes` fields, `Snapshot.OK`, concrete
initial-image instantiation, or native durable-snapshot allocation/transport
are completed by this module. Its status distinguishes those remaining
obligations accurately. The review concerns the new helper layer and does
not claim a mechanized cross-prover correspondence theorem.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
