import LeanPaperStock

/-!
The actual generated paper RISC-V model, adapted to the pinned free V1 runtime.
`LeanPaperStock` is the historical generator module prefix. Its execution API
is under `LeanPaperStock.Functions`; provenance and regeneration are recorded in
models/riscv and docs/Sail-generation.md.

Execution retains the paper's two fixed reservation predicates as `Platform`
parameters. Source correspondence, the machine's event handlers, devices,
power transitions and MachCSL adequacy are separate obligations.
-/
