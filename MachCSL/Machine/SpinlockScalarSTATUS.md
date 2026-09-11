# Straight-line spinlock register instructions

Seven actual decoded instructions are covered: unsigned immediate hart
comparison, AUIPC, address adjustment, constant one, register copy, word
sign extension and word increment. The expected post-register file states
the single changed register using the exact source bitvector operations;
every other register stays arbitrary. Word arithmetic retains truncation
and sign extension, including overflow behavior.

The checked evaluator accepts only owned register events and certifies the
actual generated `execute` dispatch. Its soundness theorem yields an
`ExecPlan` with the exact successful retirement and post-register file.
No whole-cycle, memory or branch behavior is asserted here.

The component build passes 399 jobs. Independent source review and a fresh
full type/body dependency audit passed for all 13 declarations, standard
three axioms only, no unsafe/partial dependency and zero exclusions. See
`docs/reviews/spinlock-scalar-review.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
