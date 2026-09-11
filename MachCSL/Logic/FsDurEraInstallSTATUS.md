# Logged-era filesystem installation

Frozen bounded port of `iris/FsDurSnap.v` lines1656–1710 at `arxiv-v1`
(`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). Three modules provide five
named laws: the three source bridges plus specification/capacity wrappers.

`fs_home_blocks_phi_map` equates the actual finite-set big-operator of
`FsBlocks.block` ownership at the provided `Names.bytes` with the flat
byte ledger at `FsBytesGamma.logged`. It uses the frozen byte-view
conversion and the guarded full-block flattening theorem. Its only
length premise is exactly the source's 1024 bytes for every home block.
Signed block indices and arbitrary finite home sets remain unchanged.

The footprint installation takes the exact source Shape, positionwise
run disjointness, and inclusion in the flattened restricted home map.
It consumes the logged home-block resource and returns the filesystem
footprint at the same view together with precisely the map difference.
The whole-state variant additionally consumes the supplied ghost half;
its output retains the same names and exact remainder. No link/top
ownership is inferred from bytes or silently added.

The concrete wrapper uses the existing Disk12 and FsLink23 capacities.
Logged and snapshot byte families use explicit names at the same native
Disk camera. No fresh name, camera, world, allocation, or physical-memory
update occurs. The three proofs do not invoke the transport mint or any
initial constructor. They do not assert that an unconstrained logged map
equals a cache, physical disk, or durable map.

Validation: `python3 tools/lake.py build Xv6.Fs.SnapshotCoverageProofs
MachCSL.Logic.FsDurEraInstallLink` passes 457 jobs. A fresh physical-origin
audit checks all 14 declarations in these three modules and their full
transitive types, opaque/theorem bodies (`allowOpaque := true`), and
constructor fields. Only `propext`, `Classical.choice`, and `Quot.sound`
occur; no unsafe/partial semantic dependency, zero exclusions. Explicit
rejection of `FsDurSnapshot.Initial` dependencies passes. Working audit:
`/tmp/xv6-lean-research/FsDurEraInstallOwnerAudit.lean`.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.

Actual boot configuration, inode-region/resource routing, collection,
WAL invariants, and the full crash protocol remain subsequent source
dependencies. This installation bridge does not claim those integrations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
