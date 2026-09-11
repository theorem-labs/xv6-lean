# Independent annotated-pool review

Reviewer: OpenAI Codex subagent `lean_logic_audit`, independently reviewing
coordinator-authored `AnnotatedPoolDefs` and `AnnotatedPoolProofs`. Result:
**PASS for the conditional erasure/lifting framework**. No code changes
requested.

`Pool` adds one proof label to each actual expression. Erasure keeps the
whole `State` and maps only those pairs to their expression components.
`AStep.atomic` requires an actual `Machine.Step`; its successor replaces
exactly the selected expression and appends the annotated forks after the
unchanged right context, matching native `PoolStep.atomic`. Observations
are unchanged. `ASteps` preserves the exact event count and concatenates
observation lists in the same order as native `PoolSteps`.

`erase_split` identifies the selected occurrence by its complete list prefix,
including when identical expressions occur more than once. It does not assume
CPU or expression uniqueness. `lift_step` uses that exact split, feeds the
actual primitive step to `Covers`, and reconstructs the same pool context and
fork list. `lift_steps` then threads the concrete invariant witness through
each actual step, preserving step count, final erasure and all observations.

`Covers` is appropriately an explicit application obligation. It quantifies
over every actual successor, observation list, fork list and list context
from an invariant-satisfying configuration. No global instance silently
assumes it. Its existence is not proved for a spinlock protocol in these
files. An unsatisfiable invariant or missing initial witness cannot produce
a closed application theorem. The eventual gate must construct both initial
annotations and `Covers` from the concrete control/memory/reservation/device/
power transition proofs; invoking the generic lift alone does not establish
exclusion or resource transfer.

Rebuilt the frozen target successfully (329 dependency jobs). A fresh
physical-origin audit includes every declaration in both modules and follows
type, body and constructor dependencies: all 30 declarations use only the
standard foundational axioms, with no unsafe/partial semantic dependency and
zero exclusions. Evidence is `/tmp/xv6-lean-research/AnnotatedPoolAudit.lean`
and `annotated-pool-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
