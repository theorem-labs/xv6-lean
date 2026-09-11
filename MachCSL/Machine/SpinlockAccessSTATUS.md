# Actual generated spinlock data-access plans

The seven `SpinlockAccess*` Lean modules prove interruptible `EventPlan`
plans for the five data/fence instructions of the literal seventeen-instruction
integration image: AMOSWAP.W.aq at index 7, LW at 10, SW of the incremented
counter at 12, FENCE rw,w at 13, and SW zero to unlock at 14. `SpinlockAccessImage`
connects each plan's generated `execute_*` function to the actual decoded image
instruction. This image is the separate two-hart integration program, not the
pinned xv6 kernel binary.

`Static` fixes only reset misa, mstatus, menvcfg, mseccfg, Machine privilege,
the boot PMA list and disabled HTIF address. `Static.ofBoot` derives it from
the existing universal boot family. It does not constrain PC, nextPC,
counters, general-purpose operands, PMP addresses or unrelated PMP config
bits. `BootPmp.Off` supplies the actual generic PMP check plan. Instruction
plans additionally require x10 to contain 0x80001000. The two concrete data
addresses are the lock there and the counter at +4.

The PMA, pointer-mask address transform, translation, PMP, MMIO classification
and effective-address announcement are actual generated computations.
`mem_write_ea` is faithfully treated as the generated check-only announcement:
its `write_ram_ea` builtin emits no memory-write event. The physical wrappers
preserve exact four-byte requests, all flag fields and arbitrary values. The
virtual wrappers prove alignment, page-boundary splitting and Bare translation,
retaining the generated register reads and exception checks. Full-word
assembler/extractor equalities are ordinary BitVec proofs.

AMOSWAP has a reserved/acquire read followed by two actual x15 reads (the second
is the generated eager AMOCAS-condition operand read), a conditional normal-
strength write, and a sign-extended old-value write to x15. The word to store is
the low 32 bits of the original x15. Every permitted old word and intermediate
protocol state is retained. The selected write proof mode carries exactly the
snapshot created by the exclusive read and the proved bound 4 < 2^64. Its
`writeEnabled` and `writeModeEnabled` obligations quantify over those actual
read successors. Successful write clears the reservation. No fused atomic
event, predetermined read result, chosen memory view or forced empty log is
introduced.

LW preserves the plain-read reservation and sign-extends into x16. SW reads
x16 and stores its low word; SW zero uses architectural zero independently of
the generated register carrier's unused x0 field. The fence is exactly
`Barrier_RISCV_rw_w`, whose `fenceDrains` value is false. Its plan preserves the
reservation and supplies no publication receipt. Register updates use the
actual generated register functions and preserve unrelated registers.

The principal generated source mappings are `Mem.lean:399–613`
(`checked_mem_read`, `mem_read`, `mem_write_ea`, `checked_mem_write`,
`mem_write_value`), `VmemUtils.lean:236–460` (address/virtual wrappers),
`PhysMemInterface.lean:292–355` (RAM builtin effects), and
`InstsEnd.lean:16990`, `17449`, `17504`, `17868` (STORE, LOAD, FENCE, AMO).
These are the repository's pinned generated Sail model. The paper's RAM event
rules remain the previously ported `HartEvents.v`/`HartSMem.v` rules at
`.upstream/xv6iris` arxiv-v1 `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
No generated model, existing machine rule or existing resource family changed.

These are pure, relation-parametric execution plans. Applying the native
`EventPlan` fold still requires the concrete lock protocol's resource callbacks,
request eligibility and terminal continuation WPs. The callbacks must pay the
actual memory/TSO transformations and reservation custody. Blocked retries and
dead generations are handled by the existing native event rules, not excluded
by these plan statements. This slice does not prove the concrete lock invariant,
two-hart exclusion, fairness, a positive two-hart schedule, or kernel safety.

Validation: `python3 tools/lake.py build MachCSL.Machine.SpinlockAccessImage`
passes all 425 dependency jobs. Representative rebuilt module times were
2.6 s (prefix proofs), 2.0 s (physical plans), 1.4 s (virtual plans), 1.2 s
(AMO/fence), and 1.0 s (LW/SW). The final incremental build took 2.10 s with
1,835,812 KiB peak RSS. A fresh physical-origin audit checked every one of the
233 declarations across the seven modules, including private/generated helpers,
and traversed their type/body dependency cones. Only `propext`, `Classical.choice`
and `Quot.sound` occur; no unsafe/partial logical dependency was found and zero
declarations were excluded. All proofs are kernel checked; no `sorry`, custom
axiom, native decision proof or generated-semantics modification is used.

The initial AMO elaboration exposed a slow conversion at the same-width signed
extension of its store word. An explicit checked helper now transports the
physical write plan to that exact generated expression; the final module
builds in 1.2 s. No operation or premise was changed to solve the performance
problem. Independent review remains a separate integration step.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
