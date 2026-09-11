# Native inode-region allocation prelude

Status: frozen; source-owner build and full dependency audit passed.
Coordinator source review passed; post-refactor independent audit pending.
Baseline: xv6iris `arxiv-v1`, `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
Complete boundary inventory: [inode-region-bootstrap.md](../../docs/design/inode-region-bootstrap.md).

The ten Lean modules implement the actual native record camera and the
record/marker/byte-factorization stages needed before the complete region
invariant can be installed. They do not assert the full `ireg_alloc` result.

| Source | Lean counterpart |
| --- | --- |
| Xv6Cameras.v `iregG`; InodeRegion.v 1295–1408 | `RecordRA`, generic `Capacity`, fractional/full authority and elements, `dinodeAt`, existential `imark`, `out`, `couple` |
| IcacheBoot.v 306–373 | `initialRecords`, `initialMarkers`, `initialMap`; complete lookup/domain laws, negative-key membership, disjointness, full-map coupling |
| IcacheBoot.v 736 onward record-map allocation stage | `boot_allocate`: one fresh record map, both original full record and marker elements per unsigned inum, same arbitrary frame |
| IcacheBoot.v 265–281 | `decodeRecords`, `decodeImage`, `image_decode`: arbitrary full input bytes, exact 16-record well-formed decoding and complete encoding roundtrip |
| InodeRegion.v 2778–2798 | `recs`, `recs_block`, `recs_logged_block`; exact 16 native 64-byte runs equivalent to the supplied full logged block |
| IcacheBoot.v 643–760 byte/record prelude | `bootstrap_prelude`: retains the exact decoding and six image facts, supplied byte ownership factored into record runs, fresh record authority, both fragment families and the original frame |

The source record carrier permits malformed records. Marker allocation uses the
source all-zero scalar record with an empty address list, and `imark` hides the
value existentially. Normal inode records use the actual decoded values. Signed
record keys and negative marker keys are retained; only conversion to the source
32-bit unsigned inode identifier requires `16 * nib ≤ 2^32`.

`FsInodeRegionLink` extends the existing **LockSet** registry at slot 27. Slot 26
remains the actual held-set camera; slots 0–26 and 28 onward are preserved.
Explicit record, held-set, lock, top, link, UART, invariant and machine capacities
are exported. Generic proofs work at a supplied `Capacity GF`; the link neither
allocates an invariant world nor changes any existing registry definition.

The byte proofs use the same supplied view and values. The concrete logged
specialization uses the existing Disk camera at slot 12. Only the record map is
allocated. No replacement disk authority, native durable initializer, pure
snapshot oracle, custom axiom or unchecked computation is used.

Validation: the combined `FsInodeRegionBytesProofs` / `FsInodeRegionLink` build
passes all 465 jobs. The ten modules export 56 named laws. The physical-origin
audit checks all 217 logical declarations, including private and generated facts,
and recursively traverses types, opaque bodies and inductive constructors. Only
`propext`, `Classical.choice` and `Quot.sound` occur; no unsafe/partial dependency
or `FsDurSnapshot.Initial` constructor occurs in any logical cone. The one
excluded root is the compiler-generated runtime companion
`decodeRecords._unsafe_rec` of the safe, structurally recursive decoder. The safe
decoder and all its theorem dependencies remain audited. Audit source:
`/tmp/xv6-lean-research/FsInodeRegionOwnerAudit.lean`.

Remaining source obligations: complete `ireg_slot` including reference counts,
freeze/mark/escrow/receipt rows; inode-region covering registry; boot shelter and
pending protocols; `ireg_body`/`ireg_reg`/`ireg_inv`; full `IcacheBoot.ireg_alloc` and
subsequent sealing. The eleven source resources are inventoried explicitly in
the design document rather than replaced by abstract BI parameters here.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
