# Independent spinlock control-plan review

Reviewer: OpenAI Codex subagent `lean_logic_audit`, independently reviewing
coordinator-authored `SpinlockControlDefs.lean` and
`SpinlockControlProofs.lean`. Result: **PASS for the stated instruction-plan
scope**. No changes requested.

I checked the actual generated definitions and the pinned Rocq output
`.upstream/xv6iris/model-xv6iris/rv64d.v` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`: `jump_to` at 25784,
`execute_JAL` at 41452, `execute_CSRReg` at 41802 and `execute_BTYPE` at
41853. Their Lean counterparts are in `BaseInsts`, `InstsEnd` and
`ZicsrInsts`, with the actual fixed extension check in `AddrChecks`.
This is a source comparison and a proof about the generated Lean program;
it does not establish whole-model cross-backend correspondence.

- The hart-ID instruction is the actual `CSRRS x5,mhartid,x0` AST at
  index 0. Its source access classification is read-only; the checked
  program includes privilege checking and the actual CSR callback. The
  public rule assumes only machine privilege, permits arbitrary values of
  every other register, and changes exactly `x5` to the current `mhartid`.
- `jump_plan` covers each of the 17 concrete instruction addresses, under
  the explicitly stated reset-MISA fact. Its conclusion preserves all
  registers except `nextPC`. The extension/alignment checks remain part
  of the actual `jump_to` program.
- The selection branch at index 2 handles both values of `x6 == 0`, with
  taken displacement +56 reaching index 16. The retry branch at index 9
  handles both values of `x15 != 0`, with the signed 13-bit displacement
  −12 reaching index 6. The untaken case preserves the existing register
  file, including `nextPC`; instruction retirement remains outside these
  local plans.
- `jal_zero_plan` retains the source read of `nextPC`, then the read of
  `PC` and actual jump. Destination `x0` suppresses the link-register
  write. The index-15 loop jump uses displacement −36 to index 6; the
  index-16 park jump uses displacement zero. The plans do not advance
  `PC` themselves or imply scheduler fairness.

The two checked helper computations are certificates for
`registerPlanRun`, whose soundness induction produces actual `ExecPlan`
constructors. That evaluator rejects non-register events and both
asynchronously modified pin registers. The metaprogram emits equality
reflexivity terms; Lean's kernel checks the reduction. It is not an
executable-only test or a native decision axiom.

Rebuilt the frozen target successfully (399 dependency jobs). A fresh audit
selected both modules by physical origin, including private declarations,
and traversed types, bodies and inductive constructors. The result was
37 declarations, only the standard foundational axioms, no unsafe/partial
semantic dependency and zero exclusions. Scratch audit and output:
`/tmp/xv6-lean-research/SpinlockControlAudit.lean` and
`spinlock-control-audit.log`.

These are instruction-body plans with explicit preconditions. Concrete
fetch/decode, boot postconditions, clock/cycle composition, memory/AMO
resource callbacks and all-transition exclusion are separate obligations.
No closed spinlock gate follows from this slice alone.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
