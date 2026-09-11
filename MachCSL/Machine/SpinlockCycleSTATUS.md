# Actual cycle composition for the spinlock image

The generic cycle theorem wraps an interruptible EventPlan for the actual
decoded instruction. It proves the generated active-hart path, including
machine interrupt dispatch for arbitrary pin results, exact fetch/decoder,
landing-pad check and default nextPC write. The instruction proof must
establish successful retirement and retain active-hart state; clock
composition additionally requires the actual zero menvcfg postcondition.

The wrapper copies nextPC to PC, follows the real retirement-enable flag
and modular counter increment, and covers both clock choices and arbitrary
cycle-counter filters. Its postcondition retains every instruction outcome
and gives the exact completed register transformation. It preserves the
instruction's final reservation and protocol indices. The later hart
restart event and concrete protocol/family invariants remain separate.

Build: 424 jobs, proof module about one second. Independent source review
and complete type/body dependency audit passed for all 16 declarations,
standard three axioms only, no unsafe/partial dependency and zero exclusions.
See `docs/reviews/spinlock-cycle-review.md`. This conditional composition
theorem does not by itself close the two-hart gate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
