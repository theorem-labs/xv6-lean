# Same-name durable installation review

The coordinator read all four FsDurInstall modules and compared the exact
source installation and home-map laws in FsDurXfer.v. The 448-job build and
independent audit of all 40 physical-origin declarations pass. The audit
traverses types, opaque bodies and constructor fields; only the standard three
axioms occur, with no unsafe/partial dependency or excluded root.

The input map is split at the exact run union, and the finite-map difference
is returned at the original byte name. Reassembly is an equivalence. A real
exclusive footprint supplies the nonvacuity facts. The whole-state rule takes
the ghost half explicitly. Home flattening requires exactly full 1024-byte
blocks; no malformed overlapping-map correspondence is asserted. The source
snapshot authority supplies agreement, and no allocator is used.

Approved for integration. This provides resource installation, not the live
boot instruction proof or crash refinement.

Reviewed Lean source hashes (SHA-256):

```text
bdc04d6769957198d026cc7cf247f0f069c7099ad9f3527cb429b0d6e1ab165a  MachCSL/Logic/FsDurInstallDefs.lean
7012fb6d5f1529a541d805aa57830a489ce1c7de9eb95a78668cc7dc05334f19  MachCSL/Logic/FsDurInstallSpec.lean
3e5b705bcb4d19df36b786c00bf14ff0d50350ff9426c3831793778537349571  MachCSL/Logic/FsDurInstallProofs.lean
ab59060eada2da004326a3943c099436216dad051d1828efef6b69a3c9b63837  MachCSL/Logic/FsDurInstallLink.lean
```

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
