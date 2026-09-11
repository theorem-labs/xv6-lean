# Bitmap byte encoding review

Root independently read both BitmapEncoding modules and the pinned
`iris/BitmapEnc.v` definitions and arithmetic contracts. The signed byte index,
least-significant-bit-first integer fold, finite set polarity and full byte-image
length agree with the source. The bounds establish that conversion to an eight-bit
word does not truncate the encoded value. The roundtrip theorem preserves all
padding bits, including bits beyond the filesystem's advertised block count.

The update theorem requires agreement outside the affected byte and proves list
identity at every position. Set and clear instantiate that condition; negative
byte positions are supported by the primitive, while list updates explicitly
require nonnegative in-range positions. No issue found in this layer.

The integer AND/OR/complement arithmetic seam used by machine instruction WPs is
still outstanding. These byte-image laws do not claim that seam, bitmap ownership,
a durable snapshot, or an allocator correctness theorem. The module's 74-declaration
transitive standard-axiom audit is retained in the integration build.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
