# Bitmap encoding and full byte round trip

Source: `BitmapEnc.v:bits_to_Z,byte_bits,bm_byte,bm_bytes,bm_bytes_upd`,
its set/clear corollaries, and `FsImg.v:1821–1885` at xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The executable encoder preserves the source Int accumulator, signed byte
index and least-significant-bit order. Bounds prove that the eight-bit cast
is exact. Per-bit membership, high-bit zero, byte extensionality, list
length/lookup, byte/bit index decomposition and encoded-set range laws are
kernel proved.

`bitmapBytes_roundtrip` proves that an arbitrary list of length n is exactly
the encoding of its own `bitmapSet n`. Every one of its 8*n bits is retained,
including bits beyond a filesystem's advertised size. No clearing of padding
or metadata bit zero is assumed. Negative byte indices remain meaningful in
the primitive; a regression checks bit -1 in byte -1. Another regression
checks preservation of the top bit in a one-byte image.

The exact source one-byte replacement theorem and its finite-set insertion
and erasure corollaries are proved. They require agreement away from the
changed byte and the source nonnegative/in-range update index. There is no
implicit update outside the encoded list.

Validation: `python3 tools/lake.py build Xv6.Fs.BitmapEncodingProofs` passes
15 jobs. The embedded audit checks all 74 encoding declarations transitively,
allowing only `propext`, `Classical.choice`, and `Quot.sound`.

The separate BitmapArithmeticProofs/Link layer now proves the source integer
AND/OR/complement and machine-word value bridges. This encoding stage supplies
the full byte identity needed by durable snapshot construction. It does not
establish the remaining snapshot byte ties or native resource allocation.
No literal image or generated certificate is imported.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
