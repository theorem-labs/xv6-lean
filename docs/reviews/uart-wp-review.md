# UART worker weakest-precondition review

Result: **PASS** for the frozen `UartWPDefs`, `UartWPSpec`, `UartWPProofs`, `UartWPLink` modules and `UartWPSTATUS.md`.

The comparison used `iris/WpUart.v:782–985` at xv6iris commit `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, together with the actual Lean `Machine.UartStep` constructors. The permit retains the actual device transition, powered-on trace shape, wire/history equality, successor UART ghosts, and authoritative history resource. The ledger callback retains both masks and the transmit/no-loopback or arbitrary environmental receive premises. No byte assumption restricts RX. Loopback transmit and latch/idle remain silent.

The native proof opens the UART invariant only for TX/RX and the PLIC invariant only for latch. It updates the concrete full power interpretation through authority/fragment agreement, preserves the other device and memory/register components, and retains the actual IRQ-level and latch premises from the machine relation. The latch re-establishes the PLIC plan. The guarded Iris worker proof covers both live steps and dead-generation stuttering through the actual machine language. Allocation and concrete registry wiring use the implemented ghost resources; the component specification introduces no unproved implementation assumption.

Validation: independently reran `/tmp/xv6-lean-research/UartWPAudit.lean` through `tools/lake.py env lean`. All 216 UART-WP/PLIC declarations passed a transitive `collectAxioms` allowlist containing only `propext`, `Classical.choice`, and `Quot.sound` (1.58 seconds). No native certificate or custom axiom was accepted. The source comparison found no implementation correction necessary.

This review concerns the UART worker and its explicit observation permission. It does not establish the remaining MMIO/driver/client-ledger or whole-system adequacy theorems. Those limits are correctly recorded in the module status.

*Authorship note: this was researched and written by an AI coding agent (OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is posted from this account.*
