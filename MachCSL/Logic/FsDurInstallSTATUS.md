# Native durable resource installation

Frozen bounded port of `iris/FsDurXfer.v` §3e (lines1007–1090) and
`fs_footprint_install_facts`/`fs_state_install` (lines1145–1187), at
`arxiv-v1` (`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). Four modules
provide 12 named laws and concrete capacity links.

`Facts` packages the source's three exact premises: run Shape,
positionwise run disjointness, and inclusion of the run union in the
provided byte map. `remainder` is the native finite-map difference of
that provided map and the run union. Neither definition adds local inode
validity, geometry, a pure snapshot validity premise, or an allocation.

The generic map split is an equivalence. The footprint install consumes
the provided map's byte ownership, reconstructs the existing footprint
at the same view, and returns ownership of the exact difference.
The whole-state install additionally consumes the explicitly supplied
ghost half. It does not manufacture link or top tokens from byte ownership.
The nonvacuity theorem reads Shape and disjointness from a real exclusive
footprint and returns its whole run map with an empty remainder.

The home-block bridge proves that the existing `SnapshotHome.restrict`
constructor equals the native `FiniteMap.ofSetWith` map. Under exactly
the source's pointwise 1024-byte home-block premise, flattening and the
map/set big-operator laws identify full home-block ownership with the
flat byte-map ledger. `fs_home_install` composes this bridge with the
same-view install. Signed block addresses and arbitrary finite home sets
are retained; no nonnegative address, log exclusion, or extra coverage
condition is introduced.

`fs_footprint_install_facts` uses the existing snapshot-family byte
authority and its footprint to read the three pure facts. Agreement is
the actual Disk camera's lookup law. `registrySourceSpec` selects the
current Disk12 capacity; `registryInstallSpec` selects the existing
FsLink23 capacity. All input and output byte views retain their names.
No fresh name, camera, world, or initial allocator is used.

The malformed-block flattening qualification remains the one recorded
in FsDurBytes: raw ordered flattening is total, while the home bridge
proves its correspondence under full 1024-byte blocks. These installation
laws do not claim unrestricted equality with Rocq's internal map-fold
order for overlapping oversized malformed blocks.

Validation: `python3 tools/lake.py build
MachCSL.Logic.FsDurInstallLink` passes 448 jobs. A fresh physical-origin
audit checks all 40 declarations, all transitive types and opaque/theorem
bodies (`allowOpaque := true`), and referenced constructor fields. Only
`propext`, `Classical.choice`, and `Quot.sound` occur; no unsafe/partial
semantic dependency, zero exclusions. The explicit rejection of
`FsDurSnapshot.Initial` dependencies passes. Working audit:
`/tmp/xv6-lean-research/FsDurInstallOwnerAudit.lean`.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.

Source-instance mint/transport and subsequent snapshot transport and
cloning remain separate next obligations. This slice neither allocates
a runtime epoch nor proves a complete boot or crash refinement.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
