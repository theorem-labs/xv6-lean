# Actual-pool annotation transport

This generic proof framework implements the annotation strategy in
`docs/design/spinlock-exclusion-architecture.md`. A labeled pool contains
the actual machine expressions. Erasure drops only labels, retaining the
whole state, observation list, step count, ordering and actual appended
forks. An annotated step contains a real primitive step and one application
annotation transition; there is no second machine interpreter.

The erasure theorems transport annotated steps/runs to actual PoolSteps.
Conversely, the explicit `Covers` contract requires an application to
handle every actual event in every invariant-satisfying labeled context.
The lifting theorem then constructs annotations for the identical actual
schedule and preserves its invariant, including arbitrary scheduling and
forks. Neither the transition nor the invariant is installed globally.

The spinlock application must still define its concrete labels and prove
`Covers`, including blocked reservations, stale generations, PLIC pins,
devices, power cycles and holder transitions. This conditional framework
does not establish holder exclusion or close any integration gate.

Build: 329 jobs, proof module about 0.75 seconds. Independent review and
complete dependency audit passed for all 30 declarations: standard three
axioms only, no unsafe/partial dependencies and zero exclusions. See
`docs/reviews/annotated-pool-review.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
