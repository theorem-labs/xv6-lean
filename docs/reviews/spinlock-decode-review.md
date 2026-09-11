# Independent root review: actual spinlock decoder

Verdict: PASS. Codex root read both decoder modules and all seventeen closed
certificates. The expected AST table matches the literal program, including
the signed retry branch, AMOSWAP acquire bit, non-draining `fence rw,w`, and
the two backward jumps. Actual generated `ext_decode` is evaluated by the
previously proved snapshot-plan interpreter and transported to arbitrary
register files satisfying the three explicit register facts.

The snapshot includes actual reset `misa`, since the AMO decoder checks its
A-extension bit, as well as machine privilege and security configuration.
Coverage is proved for every supplied register. No execution effect is
inferred from decoding alone.

Each private certificate constructs an ordinary equality reflexivity term.
Lean's declaration kernel checks conversion against the real decoder; the
tactic does not supply an unchecked evaluation result. The Fin 17 wrapper
uses all seventeen certificates. The independently inspected negative
control substitutes a wrong AST and is rejected by the kernel.

A fresh physical-origin audit of the four image/decoder modules passed for
159 declarations, their types and full proof dependency cones. Only the
standard three axioms occur; no unsafe or partial semantic dependency and
zero excluded declarations. The image byte/readback review is recorded
separately in `spinlock-image-review.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
