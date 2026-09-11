# Native running-context load review

The coordinator read all four modules and the exact running-context and
physical-byte source definitions, plus the clean/dirty load proof. The 421-job
build passes. The independent combined audit checks all 70 declarations and
full opaque-body/type/constructor cones with standard axioms only and zero
unsafe/partial dependencies or exclusions.

The two context names use the existing mono-nat and dirty-set cameras. The
running token retains both full authorities, its hart view receipt, bound,
watermark, and per-key authored-or-below-bound justification. Physical bytes
retain their actual heap value and matching payNone timestamp at the same
fraction. The clean arm uses the context floor; the dirty arm uses native
dirty membership and authored visibility, without assuming timestamp ≤ view.

The load derives all-view agreement from the complete heap interpretation
including metadata and the complete TSO interpretation. Its preservation
form returns those resources and the exact original context and byte. No
view, log, memory, ghost name or registry is mutated. The Era.interp wrapper
retains every other era component. Empty-context allocation is explicit and
fresh; it does not assert any existing boot-era context was allocated.

Approved as the physical native read gate. VA mappings, context store,
stack algebra, parking/migration, SIE resources and function WPs remain open.

Reviewed Lean source hashes (SHA-256):

```text
149a8cf36219fba8b4441c265c47b79401cc6250a0500e82e274a5de3dcd7d29  MachCSL/Logic/TsoContextDefs.lean
f579151918f8a97d1d9013bb15a2c1e68bb2f8b968a0140f1e91ff239fff7d52  MachCSL/Logic/TsoContextSpec.lean
ec405c93b667b013ddb18d50a65a8e010713328d7fc5ecfe1c83c88a56c09886  MachCSL/Logic/TsoContextProofs.lean
55bedfb336c6ad2f0ad2bfd70d95d2cbff6071b5181e3de352775f7047629d49  MachCSL/Logic/TsoContextLink.lean
```

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
