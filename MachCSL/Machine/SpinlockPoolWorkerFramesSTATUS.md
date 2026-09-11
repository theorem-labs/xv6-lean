# Concrete spinlock worker frames

The six theorems in SpinlockPoolWorkerFrames preserve the full pure PoolInv
across every UART and PLIC primitive and reset/dead disk primitive. The
annotated pool is unchanged. UART observations are retained, PLIC only changes
the two pin registers, and the exact reset-disk inversion proves the entire
state unchanged, including the source wild-write arm's impossible reset guard.
This covers live and stale worker cases; it does not construct global Covers.

Build501 jobs. Fresh physical/full-opaque-body audit: six declarations,
standard three axioms, no unsafe/partial dependencies, zero exclusions.
Independent concrete-pool-agent review passed; the combined worker, power-off
and coverage modules have 18 audited declarations. See
`docs/reviews/spinlock-pool-workers-review.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
