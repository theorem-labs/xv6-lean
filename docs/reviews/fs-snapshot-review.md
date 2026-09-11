# Durable snapshot and signed home-map review

Codex independently reviewed frozen `Snapshot{Defs,Proofs}` and
`SnapshotHome{Defs,Proofs}` plus `SnapshotSTATUS.md` against
`FsDurSnap.v:261–406,516–546,574–615` and `LogDefs.v:24–40,136–176` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The review passes without a
requested production correction. This review is independent of the snapshot
implementation and the owner's audit.

All 21 `snap_bytes` clauses are retained in `Snapshot.Bytes`, with the same
arbitrary durable state and finite signed block-map carriers. In particular:

- `links` retains the existential choice function, its per-node `ElemOK`,
  and actual native camera validity with the extra root token and its
  existential value. Plain-family validity is proved by taking the left
  factor; it does not replace the stronger premise.
- The inode domain and whole rounded-region domain are separate. Directory
  locality uses the exact `toNat (ninodes / 16 + 1)` width, and the width
  conversion theorem requires the explicit signed equality.
- Record locations preserve signed division/remainder and the prefix/suffix
  byte-list representation. Data and indirect-block ties quantify over all
  retained allocations, while owned-block disjointness includes the
  indirect root and allocations beyond logical file size.
- Metadata marking, owned-block marking, metadata exclusion, cross-node
  disjointness, per-node slot injectivity and superblock geometry are all
  present independently. None is silently inferred from a more restrictive
  state carrier.
- The pool starts at zero, and the complete disk-domain upper bound allows
  block zero. Negative keys are excluded by `Bytes.domainBelow`, not by the
  underlying map. `free_zero_present` correctly exposes the zero case.

`OK` is exactly byte consistency and per-inode locality; `Holds` existentially
hides the state. `Shape` correctly contains the source record's sole remaining
domain-bound field, despite the source's older header text. `InodeRead` retains
all four record/data/indirect/slot clauses. The reviewed theorems derive their
conclusions from these stated obligations; they do not claim to construct a
full initial snapshot or preserve it through arbitrary mid-operation states.

For the home map, `logRegion_mem` proves the header plus 30 slots to be exactly
`start ≤ b < start + 31` for every signed start. Coverage subtraction has no
hidden positivity or block-zero filter. `restrict_lookup` and
`restrict_enumeration` justify the ordered finite-map implementation against
the source `set_to_map` lookup law, even if an alternative enumeration repeats
a key. Repeated keys use the same total reader value. The absent-key view is
`[]`, matching source `dv_of_D`, and exact-domain reconstruction is proved.

The initial-image home and block-bound corollaries use their explicit
`BootImageWF` or `CovIn` assumptions. They do not strengthen generic home
membership. The checked zero and negative coverage examples confirm that
those keys survive restriction outside the log; the log's last included block
and first excluded block are proved separately.

Independent validation rebuilt both proof targets together: 245 jobs passed.
A fresh audit selected declarations by physical module origin, traversed
statement and proof dependencies plus inductive constructor fields, and
checked all 153 declarations across the four modules, including private
helpers. Only `propext`, `Classical.choice`, and `Quot.sound` occur. There are
no unsafe or partial logical dependencies and zero excluded runtime
companions. Records are `/tmp/xv6-lean-research/SnapshotIndependentAudit.lean`
and `snapshot-independent-audit.log`.

The documented boundary is accurate: this checkpoint supplies the complete
pure contract and generic home-map laws. It does not yet allocate native
snapshot resources, prove initial `Snapshot.OK`, or establish snapshot
transport across commits or recovery. Source correspondence is reviewed at
these definitions and lemmas; no checked cross-prover translation is claimed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
