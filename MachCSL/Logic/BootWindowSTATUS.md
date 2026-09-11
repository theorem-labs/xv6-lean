# Generic boot-window extraction

Full byte and timestamp map ownership can be extracted into any finite list of modular-address word windows with pairwise distinct selected byte keys. Every selected byte must be present and RAM; each window has its actual width. The result preserves full stored-word ownership and returns the exact original maps with only selected keys deleted. Outside lookups are unchanged.

Build418jobs; independent source review and all35-declaration full-cone audit passed, standard three axioms only and zero exclusions. See docs/reviews/boot-window-review.md. Concrete image lookup, code sharing and client initialization are separate callers.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
