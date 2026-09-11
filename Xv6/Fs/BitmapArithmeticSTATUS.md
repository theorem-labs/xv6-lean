# Bitmap integer and machine-word arithmetic

Source: `.upstream/xv6iris/iris/BitmapEnc.v:180–246`, at paper pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. This completes the three integer
arithmetic laws deferred by `BitmapEncodingSTATUS.md`, using the frozen
encoder and its bit-membership proofs.

| Rocq source | Lean theorem in `Xv6.Fs.BitmapArithmetic` |
| --- | --- |
| `bm_byte_land_pow2` | `bitmapByte_land_pow2` |
| `bm_byte_lor_pow2` | `bitmapByte_lor_pow2` |
| `bm_byte_ldiff_pow2` | `bitmapByte_ldiff_pow2` |

Every source theorem retains arbitrary signed byte index `j`, signed bit
index `k`, and the exact bound `0 ≤ k ∧ k < 8`. Lean's integer power takes a
natural exponent, so the expression is `2 ^ k.toNat`; the bound proves the
conversion exact. AND and OR use the native Iris dependency's
`FromMathlib.Int.land` and `FromMathlib.Int.lor` from `Iris.Std.BitOp`.
Complement uses Lean's signed integer `Int.not`. These are the integer
bitwise operations, including the negative complement operand. The proof
reduces them to natural-number bit extensionality after establishing the
unsigned byte's bits; it does not replace complement with subtraction in
the public statement.

`test_zero_iff` and `test_nonzero_iff` characterize block membership.
`test_block_zero_iff` uses signed Euclidean division and remainder and has
no nonnegative-block premise. The 64-bit counterparts `word_test`,
`word_set`, and `word_clear` act on the exact zero extension of the byte.
Their `*_unsigned` theorems directly identify the unsigned results with
the three source integer operations. In particular, finite 64-bit
complement agrees after AND with the zero-extended byte. `bitMask_word_shift`
also connects the mask to shifting `1#64` by the complete 64-bit encoding
of the signed `k`, under the source bound.

`word_test_block_zero_iff`, `word_set_block`, and `word_clear_block` work for
every signed block index, including negative indices. No filesystem-size
bound is introduced, so padding bits and byte positions retain the existing
encoder's meaning. These pointwise arithmetic results do not license an
out-of-range update of a finite byte list; the existing list-update theorems
keep their own bounds.

Validation:

- `python3 tools/lake.py build Xv6.Fs.BitmapArithmeticLink`: passed 29 jobs;
  the final link module compiled in 561 ms.
- `python3 tools/lake.py env lean /tmp/xv6-lean-research/BitmapArithmeticAudit.lean`:
  independently enumerated all 48 declarations physically originating in
  these two modules, including private and generated helper declarations;
  all axiom cones use only `propext`, `Classical.choice`, and `Quot.sound`.
  Traversal of all statement and proof dependencies found no unsafe or
  partial semantic dependency. No runtime companions were excluded.

There are no imported image literals or generated certificates. This is a
mathematical byte/machine-word bridge; the actual instruction WPs, buffer
ownership, and filesystem allocator correctness remain separate work. It
does not claim a mechanized cross-prover equivalence theorem.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
