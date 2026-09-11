# Literal two-hart spinlock image

The 68-byte, seventeen-instruction image is the concrete program documented
in `docs/design/two-hart-spinlock.md`. It starts at 0x80000000, places the
lock word at 0x80001000 and counter at 0x80001004, and sends harts 2–7 to
the final self-jump. The literal bytes are part of the Lean definition.

Checked theorems establish image length, every four-byte instruction read
from actual loaded RAM, initial zero lock and counter words, exact numeric
instruction addresses, physical RAM coverage and code/data separation.
All finite certificates use kernel-checked reduction. This is an image
and byte-loading result; instruction execution, exclusion and the positive
two-hart trace remain separate obligations.

Independent image review passed in `docs/reviews/spinlock-image-review.md`.
A fresh combined audit covers all 159 declarations in the image and
decoder modules and their transitive logical dependencies, with only the
standard three axioms and no unsafe/partial dependency or exclusion.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
