# Snapshot bootstrap prerequisite review

The coordinator read the complete SnapshotCoverage, SnapshotConfig and
FsDurEraInstall files and compared their exact FsDurSnap/FsCfgSnap source
sections. Target builds pass at 457 jobs for coverage/installation and 254
for configuration. The independent combined audit checks all 117 declarations
in these eight modules and their full opaque-body/type/constructor cones,
with only the standard axioms, zero exclusions and no unsafe/partial or
initial-constructor dependency.

Coverage derives domain membership for every metadata, owned and free-pool
block. Its converse sweeps the rounded inode region at index 16*(b-start),
including padding records, and requires log coverage only where the source
does. The below-size result permits zero. No stronger geometric or global
coverage assumption is added.

Record decoding uses injectivity of actual well-formed encoded records at the
same byte offset. The total node fallback has empty address and indirect
lists, exactly as in the source, and is proved different from the valid
DurableNode.zero. Raw block sets include arbitrary finite-map keys, including
keys beyond EOF and the customary slot bound. Home membership, cross-inode
disjointness, live-set union and exact spent sets are proved over signed
addresses.

Era installation is the source's logged byte view at its existing runtime
name. Full home blocks equal the flat native map, which is split at the actual
source run union. The exact remainder is returned, and the whole-state rule
requires the existing ghost half. No name or camera is allocated, no physical
disk changes, and no configuration/inode-region/bitmap invariant allocator is
claimed. These are approved prerequisites for that later native bootstrap.

Reviewed Lean source hashes (SHA-256):

```text
9bd341e342be8cdeeef8c173fa9475d9b5d09004de02dc79230adc340c050cd2  Xv6/Fs/SnapshotCoverageDefs.lean
0d7334498b4f5e85c51ac63466a6db20f8aeb9a722d30ecead759cd22abf333e  Xv6/Fs/SnapshotCoverageProofs.lean
2a00f044635b508b378e95773f654645619d6f3b1ebbd0e86f1561b3497b8e2e  Xv6/Fs/SnapshotConfigDefs.lean
cf06a295c1770c6156e8f48cd2540898686a71be64c81c5960a241d75102d368  Xv6/Fs/SnapshotConfigDecodeProofs.lean
172f46c0482d2f68d9784b31bab014ddc91122c378d7fd7077c9df6f75680a34  Xv6/Fs/SnapshotConfigBlockProofs.lean
1d38de49d1a1c78e02f995e8a99aab7869cd3a831c1d70c2bb4e8a301c75626f  MachCSL/Logic/FsDurEraInstallSpec.lean
4aa05b208ba1edfebe89766bf8e373cea2e666275aebdaad9e0782edbe90c0d0  MachCSL/Logic/FsDurEraInstallProofs.lean
52990eda04ed6edeaf63dbe9635731d9663f290120877b8767eac29fe5eba5a9  MachCSL/Logic/FsDurEraInstallLink.lean
```

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
