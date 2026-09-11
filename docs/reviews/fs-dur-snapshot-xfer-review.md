# Native durable snapshot transport review

The coordinator read all four modules and the exact pinned FsDurSnap.v
allocation, clone and registry-step laws (lines 854–926 and 1368–1380).
The 475-job build passes. A fresh independent audit checks all 17 physical-
origin declarations and their complete type, opaque-body and constructor
cones, with only the standard three axioms, zero excluded roots and no
unsafe/partial or initial-image constructor dependency.

The transfer retains the source authority, fractional filesystem state and
root token. Its only extra pure premises are the source's exact Shape and
inclusion of the source authority map in the proposed disk flattening; the
share is strictly above one half. The new epoch's authority is restricted
to bytes read from the source resources, with inclusion proved transitively.

Cloning opens an existing Pdur, reads those same premises from its native
resources, uses the checked source-instance transfer at full share, and
reconstructs the original at its original three names. Explicit resource
placement prevents the fresh authority from accidentally replacing the old
one. No physical disk or Iris world is created. The registry step takes the
next epoch itself and discards the affine old epoch, matching the source;
it does not purport to prove a filesystem commit from arbitrary bytes.

Approved for integration. Direct mint consumers remain the reviewed source-
instance footprint transfer and generic specification wrapper. The complete
runtime collection, boot installation and crash invariant remain open.

Reviewed Lean source hashes (SHA-256):

```text
a66cdc45fae7e11703a01cee0de4c4fb4595a92564a47994bf919935cd9d6e3e  MachCSL/Logic/FsDurSnapshotXferDefs.lean
7cc13b9ad78c5a81a1135172b65d28756e3f380aab20ca9afbc960ee03c3a089  MachCSL/Logic/FsDurSnapshotXferSpec.lean
e0d036f1fa4a8feba3b34c6cb5c910d403ba0af8207a947aeb17777357b7efec  MachCSL/Logic/FsDurSnapshotXferProofs.lean
5b2c69129eb963dde9cd5777fcb6a4b19553035859ef55e7afdbe3025a0578ea  MachCSL/Logic/FsDurSnapshotXferLink.lean
```

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
