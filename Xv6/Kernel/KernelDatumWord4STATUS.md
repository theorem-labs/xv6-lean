Native four-byte source datum access

Five modules implement four geometry and three resource contracts. Build:
660 jobs. Strict owner audit: 48 declarations, complete physical origins,
types, opaque bodies and constructors, standard three axioms only, no
unsafe/partial dependency and zero exclusions. Six kernel checks cover
CpuOwn definition equality, page-end geometry, rejected misalignment,
maximum-word no-wrap and nonidentity physical mapping. Independent peer
review passed with a second 48-declaration audit and seven kernel checks;
see docs/reviews/kernel-datum-word4-peer-review.md.

Actual byte ownership determines a common PPN through native map agreement;
all four claims, the physical context window and an internally funded
replacement-value wand are returned. Original virtual tier is preserved.
No translation, load/store, CPU count update or function WP is claimed.
See docs/design/kernel-datum-word4-boundary.md. Evidence is recorded under
/tmp/xv6-lean-research/kernel-datum-word4-{build,owner-audit,checks}.log.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
