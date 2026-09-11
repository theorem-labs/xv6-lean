# Independent mycpu scalar-body review

Status: independent review PASS for all five frozen modules. The sail-audit
agent owns this report only and did not edit the implementation or compete
with the owner's active builds.

Compared `Xv6/Kernel/MycpuScalar{Defs,Spec,Proofs,Link,Geometry}.lean` files with
pinned `ProofMycpu.v:70–96,155–225`, `ProcGeom.v:764–815`, the generated
`InstsEnd` instruction bodies and compressed redirections, `Regs.rX_bits`/
`wX_bits`, `PcAccess.get_arch_pc`, and `Step.run_hart_active`'s one-level
ExecuteAs selection.

The selected instruction indices are exactly 0, 3, 4, 5, 6, 7, 8, 9 and 12
of the existing fourteen-instruction table. They implement the two SP adds,
SP-to-S0 setup, TP-to-A5 copy, 32-bit ADDIW sign extension, seven-bit left
shift, AUIPC, signed ADDI, and A5-to-A0 add. Their `after` register files match
the source's per-instruction map-update chain with modular 64-bit operations.
In particular ADDIW takes the low 32 bits and sign-extends them; it does not
assume TP is a small nonnegative hart index. AUIPC reads the supplied PC.
The actual pinned `KernelConsts` immediates are `0x11` and `0xb20`, matching
the code; a source comment still mentioning `0xa86` is stale.

The six-cell footprint is sufficient for these generated bodies: x2, x8,
x15 and x10 are fully owned; PC and x4/TP retain their independently supplied
DFrac shares. No scalar body writes PC or TP. Reading architectural x0 in the
compressed move's normalized ADD produces zero without a register read event.
No extra CSR/configuration, memory, barrier, failure or nondeterministic event
is hidden by these selected instruction arms. Unrelated register values are
arbitrary, and the output file preserves them by the exact write definitions.

`body` matches the actual generated execute/ExecuteAs selection, including
one compressed redirection. `body_eq` proves equality to execution of the
normalized instruction, and the finite `RegisterPlan.Returns` proof accounts
for its actual read and write events. The native fold extracts the required
owned cells, performs each actual register WP step, and restores the full
footprint at the exact `after` file before the caller's continuation.
Fractions are retained. A generation certificate and continuation WP remain
explicit inputs; this is not an assumed resource-access callback.

This layer does not fetch or decode the image, initialize/advance nextPC,
retire instructions, process a clock/interrupt, save/restore stack memory,
execute the final JR, or prove the full source function contract. The pinned
source whole-function proof separately controls interrupts and pins TP to the
hart. These per-body rules use the actually supplied TP register value;
they do not replace that whole-function invariant. The result constructor
`Retire_Success` is the execute result, not a proof that retirement ran.

The geometry append preserves the exact source modular `mycpu_a5` and
`mycpu_ret` expressions. It composes six pure `after` state updates only, with
an explicit PC premise at the AUIPC address `0x800018c8`; it does not model
intervening fetched cycles. The existing checked literal link gives
`0x800123e8 + mycpuA5 tp`. The ordinary address formula
`0x800123e8 + 128 * cpu` is separately proved for the eight valid CPU values.
No such small-hart restriction is imposed on the primary modular expression
or scalar instruction WPs.

The final implementation puts the explicit `program` in Defs and proves
`execute_eq` against the actual generated body. Its proof builder constructs
ordinary `Eq.refl` terms; kernel checking establishes the full definitional
equality, with no assumed event-tree equivalence. The normalized plan then
uses explicit read/write constructor trees: one read and write for eight
instructions, and two reads followed by a write for the A0+A5 add. All four
geometry definitions also reside in Defs. No semantic defect was found.

The owner's final five-module build passed 502 jobs. A fresh independent run
of `/tmp/xv6-lean-research/MycpuScalarPeerAudit.lean` audits all 67 logical
declarations by physical module origin, including private helpers, types,
opaque theorem bodies and datatype constructor dependencies. All pass with
only `propext`, `Classical.choice`, and `Quot.sound`; zero roots are excluded,
and no unsafe/partial or initial-snapshot-allocation dependency occurs.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
