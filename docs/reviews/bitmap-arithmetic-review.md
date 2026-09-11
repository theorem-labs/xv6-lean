# Bitmap arithmetic review

Root independently read both BitmapArithmetic modules, the pinned
BitmapEnc.v:180–246 integer contracts, and the native Iris signed bit-operation
carrier. The three exported integer laws preserve the source's arbitrary signed
byte position and guarded signed bit offset. Conversion of the exponent to Nat
uses the explicit nonnegative guard. The complement law retains the infinite
signed complement before the AND operation.

The 64-bit bridges prove that zero extension preserves the byte and that its
bounded one-bit mask does not overflow. Test, set and clear agree directly with
the integer results. High complement bits cannot enter a result masked by the
zero-extended byte. Signed quotient/remainder wrappers correctly handle negative
indices as well as nonnegative ones. The underlying clear law happens to admit
a stronger Nat-offset statement, but the public source contract retains its
original bound. No issue found.

These are value equalities. The checked execution of the actual load, word-shift,
and store instructions, their source shift-count masks and memory ownership are
still separate instruction-WP obligations; this review does not promote the
word-shift value equality to an instruction correctness claim.

Independent build passed 29 jobs. A fresh physical-origin audit checked all
48 logical declarations and full type/body dependency cones, with standard three
foundational axioms only, no unsafe/partial dependency and no runtime exclusions.
Records: BitmapArithmeticRootAudit.lean, bitmap-arithmetic-root-build.log and
bitmap-arithmetic-root-audit.log under `/tmp/xv6-lean-research/`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
