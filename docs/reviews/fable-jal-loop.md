# Fable review of symbolic JAL and clock execution

Fable 5.1 at maximum effort found no semantic defect in the canonical-family
`Dynamic`, `override`, `retire`, `clock`, or `afterCycle` definitions. Its reading
of the 14 implementation modules agreed with the stated generated-model
correspondence. It did not run Lean or independently verify the reported audit;
the build and kernel-audit evidence below is Codex's verification.

## Invocation and review boundary

- Reviewer: Claude Code CLI, exact model `claude-fable-5-1`, `--effort max`.
- Session: `ec4fe016-29ad-484f-94a5-63ecea136874`.
- Initial invocation: `--permission-mode dontAsk`, tools limited to Read, Glob,
  and Grep. It inspected the implementation drafts, generated Sail paths,
  original CLINT source, supporting machine code, runtime, and failed probes.
- After approximately 56.6 minutes of source investigation without a final
  response, Codex interrupted that request. Its result records
  `error_during_execution` and `is_error: true`; that is not counted as a
  successful completed review. Its aggregate usage lists Fable and Haiku; the
  final review response below lists Fable alone.
- Codex resumed the same session with the same model, effort, and permission
  mode, disabled tools, and requested a bounded final assessment using the
  gathered research. The final invocation completed in 110.552 seconds with
  `subtype: success`, `is_error: false`, and model usage identifying only
  `claude-fable-5-1`.

The final prompt explicitly supplied the implementation's reported green status
and warned that it was a local zeroRegisters-derived boot-family witness, not a
proof for arbitrary `BootFacts`, power-on prestates, or global Iris safety.
The reviewer distinguished supplied build information from its own source
inspection. Raw CLI transcripts and JSON results remain outside the repository.

## Findings and disposition

| Finding | Disposition |
| --- | --- |
| Repeated symbolic boot reduction causes expensive static-register reads. | Implemented static-slice certificates and transport through `Covers`, plus RF update proofs over abstract bases. |
| The symbolic changed-mip callback guard must cover both branches; merely increasing evaluator budgets is insufficient. | `clint_dispatch_exec` splits the guard and retains callback reads through `ReadOnly`. Both branches are checked. |
| The generated retirement order, modulo counter updates, post-increment MTI comparison, disabled STCE branch, JAL next-PC writes, and x0 behavior agree with the definitions. | Accepted. Exact complete RF results and finite event traces build against the actual generated model. |
| Event composition should preserve reads and writes rather than erase them with whole-tree equalities. | Implemented `RegisterExec`/`FetchExec`, bind and ExceptT composition, and actual NodeStep embeddings. |
| Generic shape/conditional lemmas could make future proofs less dependent on elaborator unfolding. | Optional maintenance work. Current proofs build; the next universally branching event-plan layer will use explicit event constructors. No speculative rewrite was added to the frozen witness. |
| A single hart-independence projection could consolidate eight fetch certificates. | Deferred after measured projection timeouts. Eight separately checked concrete-hart certificates cover exactly `Fin 8` and build in 7.7 seconds. No stronger all-zero PMP assumption is introduced. |
| There is no existing `LawfulMonad SailM` instance. | Confirmed by a separate instance-synthesis probe. Existing checked execution bind laws suffice; no redundant monad implementation or unproved instance was added. |
| Finite schedules of completed hart cycles and pin writes remain weaker than arbitrary event-level schedules. | Kept explicit. The new local witness is not a global gate. |
| Arbitrary allowed boot prestates, independently varying pin reads, and every permitted TSO view require separate treatment. | Accepted. `BootUniversal` and the native per-event WP work address those obligations separately; neither follows from the frozen canonical witness. |

The review's detailed explanations of the earlier evaluator failure modes are
proof-engineering diagnoses, partly inferred from source rather than measured
traces. The verified result is the successful compositional proof, not a claim
that alternative reduction strategies are impossible.

## Verified checkpoint and scope

`python3 tools/lake.py build MachCSL.Machine.JalLoopWitness` passes 169 jobs.
The all-eight-hart fetch module takes 8.49 seconds measured wall clock, with
1,906,316 KB peak memory including the build invocation. An origin-based audit
checks all 794 logical declarations in the 14 modules, including private helpers:
only `propext`, `Classical.choice`, and `Quot.sound` occur, and no unsafe or partial
declaration is reachable in their combined logical dependency cone. Two generated
total-recursion runtime companions are excluded only as logical roots, following
the repository audit policy.

`boot_repeat_nodeSteps` covers all eight concrete harts and every finite Boolean
clock-choice list from the actual generated boot witness. It includes real
pure-node restarts and exact reservation clearing. The broader model allows
arbitrary preboot register files; full-system safety must preserve that choice.
The finite traces also do not establish all-successor native Iris WPs. Hardware
pin ownership, memory resources at all legal views, UART, DMA, power changes, and
whole-model correspondence remain separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
