# Full push_off code: frozen native resource component

All twelve approved pure and one native contract are implemented in five
modules. Full build871 jobs; PureProofs1.0 seconds, Proofs1.4 seconds and
Link1.1 seconds. Strict owner audit checks all72 physical declarations,
including generated/private origins, with exporting=false and complete
types, opaque bodies (allowOpaque=true) and constructor traversal.
Standard three axioms only, no unsafe/partial dependency, zero exclusions.
No sorry/custom axioms/native_decide/bv_decide. nativeSpec/registrySpec
have no supplied byte, decoder, translation or component-law premise.

CodePushOff.v is reproduced as24 explicit indexed instructions spanning
58 bytes. Ordinary kernel decide certificates establish every original
source-map byte, exact body coverage, fetch-width geometry and opcode
classification. The source bytes include the two actual acquire bytes
at+58/+59: the final four-aligned C.J at+0x38 fetches0x1101b7c5. The
additional footprint_complete theorem proves the union of all overlapping
fetch windows is exactly60 bytes, while body_coverage remains exactly58.

window_instr handles all three actual resource shapes: base four-byte
words, two-aligned compressed halfwords, and four-aligned compressed words
with an existential high half. Generic low-half arithmetic is kernel
proved. code obtains each window from KernelTextImage.nativeSpec at the
input's original tier and retains persistent text. Reusing overlapping
persistent text windows duplicates no linear allocation or timestamp.

The decoded and normalized constructor tables are explicitly only source
syntax inventory. No actual ext_decode/ext_decode_compressed correctness
or ExecuteAs equivalence theorem is asserted. Such certificates remain a
separate next proof with explicit generated register reads/configuration.
Full push_off execution, SIE CSR changes, four-byte memory WPs and enabled
capability transitions are outside this code-resource layer.

The separately authorized PushOffMycpuCalls Fin3 extension preserves the
old+0x10/+0x18 entries and adds+0x2c/3342/0x50f000ef. Its unchanged native
proofs build1,134 jobs and all34 declarations pass the strict audit. The
new call_sites theorem connects all three entries to this full family.

Source pin: fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. Sources:
CodePushOff.v full; ProofPushOff.v:284–405,617–910; InstrBytes.v:33–65;
actual imported KernelInstrs bytes and generated fetch resource definition.
Design: docs/design/push-off-code-boundary.md.

Reproduction:

- PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.PushOffCodeLink
- PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/PushOffCodeOwnerAudit.lean

Evidence: /tmp/xv6-lean-research/push-off-code-{build,owner-audit}.log,
push-off-code-frozen.json. Final independent coordinator review pending.
No umbrella or generated/upstream semantics changes.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
