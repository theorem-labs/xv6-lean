# Native spinlock cycle and loop

The actual seventeen-instruction Family plan, exact code access and concrete native protocol callbacks are composed by the native EventPlan fold. Guarded recursion uses the actual restart rule, clears reservations and handles both clock choices while retaining every owned resource across cycles.

Independent review and all2-declaration full-cone audit passed, standard three axioms only and zero exclusions. The standalone target passes569jobs; combined review build571jobs. See docs/reviews/spinlock-wp-review.md. Operational holder exclusion and the interference witness are separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
