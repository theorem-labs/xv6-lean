# Source-instance filesystem transport review

The coordinator read all four FsDurXfer modules and checked them against
FsDurXfer.v lines 1208–1357. The 463-job build and independent full opaque-body,
type and constructor audit of all 32 declarations pass with only the three
standard axioms. No unsafe/partial or Initial-constructor dependency occurs.

The pure mint is the source's explicit Shape/disjointness helper. Its runtime
caller derives those facts from fractional source ownership, derives the new
map's inclusion from actual authority agreement, and returns the source
resources. Whole-state transfer requires precisely a share above one half.
The new link/top resources use native validity read from the original links,
including joint validity with the optional arbitrary inode/type token.

The owner audit enumerates exactly two direct mint references: the resource-
derived footprint transfer and the generic mintSpec wrapper. The concrete
wrapper delegates that wrapper. This result is a reviewed caller inventory,
not a prohibition on future source-defined collection callers. Initial-image
constructors are absent from the entire dependency cone.

Approved for integration at existing Disk12, FsLink23 and FsTop25 cameras.
Physical disk mutation and complete crash preservation remain later work.

Reviewed Lean source hashes (SHA-256):

```text
da2f2c56885244db8e5b0e8f8b9df3f4bd60bbd9d2b6ae85dd33ea455a0ad801  MachCSL/Logic/FsDurXferSpec.lean
d8a39956733356ece33497eab7a5a3b7a38b38137eabfaf8ebfe94bdeedf6f49  MachCSL/Logic/FsDurXferByteProofs.lean
9c6aa65c3819197dae50c1849b8eff275167036a203821aaecc99d2e69d3c5ab  MachCSL/Logic/FsDurXferStateProofs.lean
998234524a01dad8bf735912c0f2363417549047d492d6cc39bdb4aed73bdf64  MachCSL/Logic/FsDurXferLink.lean
```

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
