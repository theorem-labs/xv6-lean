# Universal boot hart-ID review

Reviewed the frozen root-authored `MachCSL/Machine/BootHartIdProofs.lean`
and its status record against pinned `ArchReset.v:233–275`, the actual
generated `LeanPaperStock/Model.lean:219–231`, and the existing Lean
`BootProgram`, `BootUniversalDefs`, `BootUniversalRun`, and `BootFacts`.
The source pin is `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
Result: pass; no correction required for the stated scope.

The source board writes `mhartid` before the actual reset and firmware
initialization. Lean preserves this order and parameterizes the reset
vector. `projection` checks the resulting field through the real transparent
register evaluator with an arbitrary preboot register file, arbitrary vector,
and arbitrary 64-bit hart identifier. Its tactic constructs a reflexivity
proof that the kernel checks; the result is not supplied by native evaluation
or an assumed reset table. A successful projection also rules out evaluator
failure.

`run_hartid` transfers that result to every completed actual auxiliary `Run`
using the existing `registerRun_unique`. I checked that the latter follows
the operational read/write handlers and rules out other event branches from
successful register-only evaluation. The finite evaluation fuel therefore
supports a proved successful computation, rather than bounding the quantified
operational executions. `bootFacts_hartid` uses each CPU's existential run
from the full `BootFacts` predicate, without specializing its preboot file.

`bootFacts_selected` uses the actual `Fin 8` CPU bound to justify that casting
the CPU index to 64 bits cannot wrap. Its conclusion is precisely the
unsigned less-than-two selector. It retains all eight CPUs and proves no
instruction branch, scheduling exclusion, or lock correctness.

Independent validation:

- `python3 tools/lake.py build MachCSL.Machine.BootHartIdProofs`: passed
  154 jobs.
- `python3 tools/lake.py env lean /tmp/xv6-lean-research/BootHartIdIndependentAudit.lean`:
  checked all six physically originating logical declarations, including
  generated helpers, and recursively traversed every type and proof body.
  Only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms; no
  unsafe or partial semantic dependencies occur, and no runtime companions
  were excluded.

This is an independent review of the root agent's new module. The reviewing
agent previously contributed parts of the underlying boot proof library;
that dependency authorship is disclosed and this review is not claimed as
an independent reimplementation of the entire boot semantics.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
