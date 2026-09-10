# Fable 5.1 max: initial design review

Reviewer: Anthropic Claude Code, model `claude-fable-5-1`, effort `max`.
This is the reviewer's returned assessment, preserved for inspection.
Claims and recommendations are subject to [the coordinator disposition](fable-disposition.md).

The review is complete and written to `/home/jason/.claude/plans/initial-proposal-for-eventual-valiant.md`. The full record there covers both the original proposal review and the second-review request that appeared mid-session. Here is the standalone recap.

## Verdict

**Approve the current architecture with required changes.** The target is sound and well-defined: the paper tag has zero admitted proofs, no in-tree axioms, and a recorded 13-entry assumption baseline whose only non-primitive entries are function extensionality and the two LR/SC reservation predicates. The coordinator's `docs/PLAN.md` already adopts the gates from my first pass. What remains blocking is engineering on the Sail bridge and two certificates, not any mathematical obstacle.

## Decisions

- **Pin the paper tag `arxiv-v1`.** I withdraw my first recommendation to pin HEAD. HEAD's machine is TSO plus relaxed load-load ordering, a non-coherent icache, a bumped Sail pin and a bumped kernel. The theorem statement is unchanged, but the model is a different machine and in one axis weaker than the paper's. Track HEAD as an explicit upgrade epic.
- **Iris base is iris-lean at the pinned commit.** Two independent audits and an actual build confirm a real COFE solver, invariants, fancy updates, later credits, WP and adequacy, and a near-complete proof mode. Compiled axioms of the adequacy theorem are exactly the three standard Lean axioms.
- **Sail bridge is the free-monad instantiation of the V1 runtime.** Generated Sail bodies never touch state-monad operations directly, so swapping the runtime is safe. That runtime already exists in the theorem-labs lean-sail fork and passes its tests. The generator patch and a compiler pin are what is missing.
- **Direct port, no proof-term translation.** No 2026 tool produces Lean-kernel-checked terms from a Rocq development of this shape. Only generated data gets mechanical translation.
- **First closed milestone is a one-instruction image on the real machine**, then the two-hart spinlock under TSO, before any kernel proof fan-out.

## Required changes and remaining blockers

1. **Pin and build a development Sail compiler.** The released 0.20.2 binary emits the older runtime layout. The lock file pins lean-sail but not the compiler. Build from source in an isolated opam root and record the recipe.
2. **Scope the generator patch:** a free-V1 flag, alias emission, the specialization template, and emission of a `Platform` typeclass variable so the two reservation predicates become theorem hypotheses rather than axioms.
3. **Replace "establish correspondence" with concrete artifacts:** a Lean transcription of the Rocq outcome type with a proved map and result-type equivalences, an arm-by-arm table against the tag's step relation, and a CI-enforced certificate that no nondeterministic choice is reachable from the step and reset functions. The choice analysis has a definite outcome: Rocq resumes nat and range choices with any integer, Lean types them faithfully and more narrowly, and the syntactic scan finds no reachable choice, so the certificate is the deliverable, not a widening.
4. **Audit scope:** enumerate declarations by defining module including private names, enforce import coverage, and keep a separate root list for closed theorems.
5. **Measurement gate with thresholds** for image access and decoder facts under kernel reduction, since native evaluation is off the allowlist.
6. **Preserve the xv6-riscv MIT license** beside the imported binaries.
7. **Conventions before any function spec:** the slot-indexed functor list with explicit instance derivation, and the Lean replacement for the Module-Type sealed-functor idiom used in 225 files.

Two of my earlier claims are withdrawn in the record: the "every kernel-data write comes from a supervisor-mode hart" export ignores legitimate disk DMA, and cross-backend correspondence is a real obligation rather than something tests replace.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
