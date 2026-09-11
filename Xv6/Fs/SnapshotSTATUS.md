# Exact snapshot contract and home map

Source: `xv6iris` tag `arxiv-v1`, commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
The four modules are `SnapshotDefs`, `SnapshotProofs`, `SnapshotHomeDefs`,
and `SnapshotHomeProofs`. All are generic and import no image literals.

`Snapshot.Bytes state disk` is the full 21-field `FsDurSnap.snap_bytes`
record (lines 261–406). `state` is the existing arbitrary `DurableState.State`
and `disk` is its finite `ExtTreeMap Int (List (BitVec 8))` block-map carrier.
No validity or record/block-map consistency is hidden in either carrier.

| Source field | Lean field | Exact obligation |
| --- | --- | --- |
| `sk_bsz` | `blockSize` | Every present block has 1024 bytes. |
| `sk_sb` | `superblock` | Block 1 contains the state's stored superblock bytes. |
| `sk_parse` | `parse` | Those bytes parse to the state's superblock. |
| `sk_bmap` | `bitmap` | Bitmap block equals all 1024 encoded used-set bytes, including padding. |
| `sk_pool` | `pool` | Every free block in the signed interval `0 ≤ b < size` is present. |
| `sk_inum` | `inum` | Every named inode has signed index in `[0, 2^32)`. |
| `sk_repr` | `repr` | Every named node satisfies all five representation clauses. |
| `sk_rec` | `record` | There exists an inode-block byte list at `inodestart + i / 16`, with the split-shaped record at `64 * (i % 16)`. |
| `sk_blk` | `data` | Every held data-slot byte list is present at that slot's address. |
| `sk_ind` | `indirect` | A nonzero indirect address contains the exact entry-array encoding. |
| `sk_dom` | `domain` | Every advertised inode is present. |
| `sk_links` | `links` | There exist a choice function and spare-token value satisfying `ElemOK` and actual native camera validity of the whole family with the extra root token. |
| `sk_meta_used` | `metadataUsed` | All three metadata roles are marked used. |
| `sk_own_used` | `ownedUsed` | Every owned block is marked used and is not metadata. |
| `sk_disj` | `disjoint` | Two present nodes owning the same block have equal inode indices. |
| `sk_sbok` | `superblockOK` | All source superblock geometry clauses hold. |
| `sk_reg` | `region` | Every named inode is nonnegative and fits the inode-block interval. |
| `sk_slot` | `slot` | Each node's full 269-slot footprint is injective at nonzero addresses. |
| `sk_regdom` | `regionDomain` | Every inode in the whole rounded region is present, including its tail. |
| `sk_dirloc` | `directory` | All three directory-local clauses hold at the width derived from this state's superblock. |
| `sk_dombelow` | `domainBelow` | Every present disk key lies in `[0, size)`. |

The `record` existential preserves both prefix and suffix through the
existing `RecordInBlock`. The `links` existential retains an arbitrary
choice and arbitrary spare-token value; it is neither a fixed image choice
nor an assumed plain-family validity replacement. The disjointness clause
compares any two nodes, independently of their record contents or file size.
Owned blocks include retained allocations beyond file size and the indirect
root, exactly as the existing source-faithful `Node.Owns` specifies.

`Snapshot.OK := Bytes ∧ DurableState.Local` and `Snapshot.Holds := ∃ state,
OK state disk` follow `FsDurSnap.v:516–546`. The separate `Shape` record
has the source's actual single `domainBelow` field (its older prose header
describes a larger record). `InodeRead` retains the four source per-inode
record/data/indirect/slot readings (lines 605–615).

Pure laws include the geometry and local projections, the directory-width
conversion, native plain-family validity from the extra-token factor,
metadata-role separation, free-block exclusion from owned/metadata blocks,
cross-inode disjointness, sized/real data blocks, record-slot fit, and absent
negative or oversized disk keys. No full snapshot is constructed yet.

`SnapshotHome` follows `LogDefs.v:24–40, 136–173`:

- `logRegion` is exactly the header plus 30 slots: membership is proved
  equivalent to `start ≤ b < start + 31` for arbitrary signed starts.
- `homeSet` is coverage minus that region, with no implicit positivity or
  block-zero filter.
- `restrict` builds a finite map from covered keys and the total block
  reader. Its exact lookup and enumeration-independence theorems justify
  the concrete ordered set representation, including repeated equivalent
  keys in an alternative enumeration.
- `view` returns `[]` at a missing key, retaining the source's junk-tolerant
  default. `restrict_view` proves reconstruction under exact domain equality.
- Initial-image metadata/data home membership and size/positivity bounds
  are derived from the explicit `BootImageWF` or `CovIn` hypotheses.

Block zero is handled deliberately: `Snapshot.Bytes.pool` quantifies from
zero, and `domainBelow` permits zero. Only an explicit `CovIn` premise
excludes zero from an initial home map. Kernel-checked generic examples show
that covered zero and negative blocks survive ordinary `homeMap` restriction
when they lie outside the log. The 31-block boundary is also proved exactly.

Validation: `python3 tools/lake.py build Xv6.Fs.SnapshotProofs` passed
243 jobs (new proof module 1.1 seconds), and the `SnapshotHomeProofs` target
passed 32 jobs (845 milliseconds). Enforced namespace audits cover all 73
snapshot and 79 home-map declarations. A separate physical-origin audit
passed all 153 declarations in the four modules and their transitive type/body/constructor-field
dependencies, allowing only `propext`, `Classical.choice`, and `Quot.sound`
and rejecting unsafe/partial logical dependencies. No `sorry`, custom axiom,
`native_decide`, or `bv_decide` is used.

Independent root and peer reviews passed; see docs/reviews/fs-snapshot-root-review.md
and docs/reviews/fs-snapshot-review.md.

Next obligation: source §11a–b's record-byte and indirect-byte image ties,
then the remaining bitmap/used-set/disjointness/coverage facts needed to
construct `Snapshot.Bytes` and prove the full initial `Snapshot.OK`.
The record's fields are obligations, not assumptions silently discharged
by their presence in the definition. No initial `snap_ok` theorem or native
snapshot resource allocation/transport is claimed by this checkpoint.
Frozen FS and link modules were not modified.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
