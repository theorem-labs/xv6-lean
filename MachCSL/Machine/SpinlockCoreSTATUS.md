# Spinlock core-register family

Implemented Core from arbitrary actual boot witnesses, excluding PC and operand values, and preservation under the program's permitted register writes, retirement/clock choices, cycle projections and actual PLIC pin writes. Final PC and nextPC are the completed instruction's nextPC; instruction-address membership remains an explicit premise.

Build: 429 jobs. Independent review and fresh full-cone audit: 79 declarations, standard three axioms only, no unsafe/partial dependency and zero exclusions. See docs/reviews/spinlock-core-review.md.

Operand/phase invariants, memory instruction composition, PC reachability and complete pool coverage remain open. This component closes no integration gate or whole-system root.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
