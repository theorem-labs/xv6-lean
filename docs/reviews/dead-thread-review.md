# Independent review: dead-generation native WP

Reviewer: Codex coordinator. Read the complete DeadThread modules, the source
`RiscvExec.v:198–263` and native Iris `wp_lift_step`.

The generation extractor covers exactly the four worker families and excludes
the power thread. Actual dead arms are reducible; the uniqueness proof excludes
every live arm and forces the silent self-loop with no forks or state change.
The strict generation bound is read from the fixed state's authoritative ghost
using the death receipt. It is not an assumed property of a chosen state.

The WP proof uses native guarded Löb and `wp_lift_step` at NotStuck. It restores
the original fixed/era/trace resources after every silent step, restores the
mask, and proves the empty fork obligations. Arbitrary postconditions are
appropriate for this language's empty value type and the source nonterminating
worker semantics. No rule permits a failing live hart to stutter.

The final registry wrapper supplies the concrete invariant and machine
capacities. A fresh independent38-declaration cone audit passes with only the
three standard axioms. Review: PASS for the corpse rule. Live instruction/device
rules and initial whole-machine WPs remain separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
