# Actual spinlock decoder certificates

`SpinlockDecodeDefs.instruction` gives the seventeen intended ASTs for the
literal words in the separate `SpinlockImage` image. `decode_certificate`
proves every case against the actual generated `ext_decode` and
`encdec_backwards`; the CSR and AMO cases are included. `decode_plan` applies
the checked snapshot evaluator's existing soundness theorem to obtain native
`EventWP.Returns` for an arbitrary read predicate and arbitrary register file
with the three explicitly stated snapshot fields.

The decoder snapshot supplies Machine privilege, zero `mseccfg`, and reset
`misa = 0x800000000014112d`. This third field is necessary for this certificate:
`amo_encoding_valid` checks `currentlyEnabled Ext_Zaamo`, whose fallback
checks `Ext_A` by reading `misa.A`. The previous JAL-only snapshot did not
cover that read. The generated Zicfilp checks also retain their actual
privilege/security reads. `decodeSnapshot_covers` proves each supplied
register agrees with the real register file. No unavailable event or memory
read is silently assigned a value.

The generated decoder comes from the pinned Sail paper model. Relevant source
symbols are `DecodeExt.ext_decode`, `InstsEnd.encdec_backwards`, and
`PlatformConfig.amo_encoding_valid/currentlyEnabled`. CSRReg matches the
Zicsr clause and the AMO is `AMOSWAP`, acquire true, release false, word width
4, destination/source x15, address x10. This is a new integration image;
it is not an assertion that these bytes are the xv6 kernel or a source
spinlock implementation.

Each of the seventeen private closed certificates constructs only an ordinary
`Eq.refl` proof term, which the declaration kernel checks against the full
claimed decoder equality. This avoids expensive preliminary Meta.isDefEq
normalization and repeated conversion under a dependent Fin case split.
A separate deliberately incorrect CSR-to-JAL certificate, using the identical
tactic, was rejected by the kernel with a declaration type mismatch.

Validation:

- `python3 tools/lake.py build MachCSL.Machine.SpinlockDecodeProofs`: 398 jobs,
  proof module 1.7 seconds, command 2.67 seconds and approximately 1.99 GB
  peak RSS in the recorded run.
- `/tmp/xv6-lean-research/SpinlockDecodePerfEach.lean`: all seventeen closed
  certificates and their axiom reports, 1.68 seconds.
- `/tmp/xv6-lean-research/SpinlockDecodePerfNegative.lean`: expected kernel
  rejection of an incorrect AST.
- `/tmp/xv6-lean-research/SpinlockDecodeAudit.lean`: all 159 physical logical
  declarations across the two image and two decoder modules, including
  private/generated helpers, passed the standard three-axiom allowlist and
  recursive type/body dependency checks. No unsafe or partial dependency,
  and no excluded runtime companion.

This layer proves decoding and its register-event plan. Instruction execution,
atomic-memory behavior, lock invariants, mutual exclusion, counter evolution,
and all-schedule machine safety for this image remain separate obligations.

The root agent supplied the initial image and AST table. The artifact-audit
agent corrected snapshot coverage and completed the checked decoder proofs;
this record is implementation validation, not an independent decoder review.
The subsequent full root review and fresh audit passed; see
`docs/reviews/spinlock-decode-review.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
