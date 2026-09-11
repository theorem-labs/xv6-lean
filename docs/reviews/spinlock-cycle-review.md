# Independent generic spinlock cycle review

Reviewer: OpenAI Codex subagent `lean_logic_audit`, independently reviewing
coordinator-authored `SpinlockCycleDefs` and `SpinlockCycleProofs`. Result:
**PASS for the conditional instruction-to-cycle composition**.

I compared the actual generated `Step.run_hart_active`, `Step.try_step`,
`PcAccess.tick_pc` and `Machine.cycle`, with the pinned Rocq counterparts in
`model-xv6iris/rv64d.v` at lines 43180, 43280 and 16044
(arxiv-v1 `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). The new proofs compose
the existing universal fetch/decode, interrupt and clock plans with the actual
instruction tree. They do not install another execution function.

`active_plan` requires the precise static/PMP facts and an actual EventPlan
for the decoded instruction at the prepared register file. The real interrupt,
fetch, decode, landing-pad and default `nextPC := PC+4` operations remain in
the tree. Its successful-retirement premise rules out failure/redirection
branches by a proved instruction plan, rather than by selecting a hardware
successor. That premise must still be discharged for every concrete instruction
and protocol result.

`try_step_plan` computes the real retirement-enable value from arbitrary
counter configuration, requires the instruction's actual active-hart
postcondition, retains both active-state reads/assertion and the `tick_pc`
sequence, and covers both retirement-increment Boolean outcomes. Incrementing
uses the actual modular bit-vector operation; no no-overflow assumption is
present. `tick_pc_plan` includes the callback's read of the newly written PC.

`cycle_plan` covers both tick choices. Its clock-on branch uses the existing
clock theorem at the completed register state after PC/retirement updates,
with only the explicitly required `menvcfg = 0` postcondition. The theorem
preserves the returned reservation and protocol indices, names the actual
completed instruction state existentially, and identifies the final whole
register file with `finish tick completed`. It does not replace arbitrary
counter/pin/timer branches by a single chosen execution.

Validation: rebuilt the frozen target (424 dependency jobs), then independently
audited all 16 physical declarations across both modules, including the private
prefix helper, and their type/body/constructor dependency cones. Only
`propext`, `Classical.choice` and `Quot.sound` occur; no unsafe/partial semantic
dependency and zero exclusions. Evidence:
`/tmp/xv6-lean-research/SpinlockCycleAudit.lean` and
`spinlock-cycle-audit.log`.

No corrections requested. Concrete instruction postconditions, full-image code
access, protocol-resource callbacks, cyclic family preservation and all-pool
coverage remain separate obligations. This generic cycle theorem alone is
neither a closed safety result nor an exclusion proof.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
