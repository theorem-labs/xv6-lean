# Spinlock scalar execution independent review

Reviewed the root-authored frozen `SpinlockScalarDefs.lean` and
`SpinlockScalarProofs.lean`, including the seven selected ASTs, against
actual generated `InstsEnd.execute`, `execute_UTYPE` (16967),
`execute_ITYPE` (17479), `execute_ADDIW` (17965), `Regs.rX_bits/wX_bits`,
and the native `registerPlanRun` evaluator and soundness theorem.
Result: pass; no correction required for this execution-plan slice.

The selected image indices are exactly 1, 3, 4, 5, 6, 8 and 11. Their
post-register files match the generated operations: unsigned SLTIU of x5
against sign-extended immediate 2 into x6; AUIPC using the current PC and
shifted immediate into x10; ADDI -12 into x10; ADDI from architectural x0
into x14; ADDI 0 from x14 into x15; and the two ADDIW operations that
truncate to the low 32 bits before sign-extending into x15/x16. The x0
source is represented by actual zero, not an assumed register-file entry.
Bit-vector addition retains wraparound. Unrelated registers are preserved
by the actual dependent `Sail.Registers.write` operation.

`checked` quantifies over every register file and platform, without a
canonical reset table or fixed operand values. Each finite instruction
case supplies ordinary reflexivity evidence, which the kernel checks
against the full transparent generated execution and register evaluator.
The evaluator rejects unsupported events and both asynchronous pin keys;
its successful result therefore cannot silently discard a memory event,
barrier, pin read, or error. `execute_plan` uses the existing proved
soundness theorem and exposes an arbitrary read predicate, the exact
`Retire_Success` result, and exact `after` register file.

The fuel bound establishes a successful finite evaluator run, not a
restriction on operational schedules. These theorems execute the decoded
instruction bodies only. Fetch/decode composition, cycle PC/counter
updates, branches, memory instructions, and complete native instruction
WPs remain separate. No mutual-exclusion or image-safety conclusion is
claimed by this pair of files.

Independent validation:

- `python3 tools/lake.py build MachCSL.Machine.SpinlockScalarProofs`: passed
  399 jobs.
- `/tmp/xv6-lean-research/SpinlockScalarIndependentAudit.lean`: all 13 physical
  logical declarations in both modules, including generated helpers, and
  their recursive type/body dependency cones passed. Only `propext`,
  `Classical.choice`, and `Quot.sound`; no unsafe/partial semantic
  dependency and zero excluded runtime companions.

This reviewer did not implement the scalar modules. The reviewer did
contribute adjacent decoder/fetch proofs and earlier memory/boot libraries;
that dependency authorship is disclosed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
