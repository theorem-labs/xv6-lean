# Native mycpu scalar instruction rules

The five MycpuScalar{Defs,Spec,Proofs,Geometry,Link} modules prove the nine
register-only arithmetic instruction bodies at original instruction indices
0,3,4,5,6,7,8,9,12. The remaining four memory bodies and final JR are separate.
Source contracts are ProofMycpu.v:59–317, ProcGeom.v:772–815 and the pinned
generated InstsEnd execution definitions. Existing image/decoder certificates
supply the actual compressed and normalized instructions.

The explicit finite register program is certified definitionally equal to the
actual generated execution. Its exact event trees retain the actual TP read,
PC read, two-input ADD reads, and every GPR write. The real compressed
ExecuteAs selection is included; no alternate evaluator or handler is assumed.
The six-cell footprint owns full SP/S0/A5/A0 and independently fractional or
discarded PC/TP. Every other cell is unowned by this package. The symbolic
register file has arbitrary values and is not an initial/reset snapshot.

Native wp_scalar uses RegisterPlan.fold on the actual body and returns the
same named footprint with precisely its proved updated values. Generation
and actual continuation WPs are retained. No full-register ownership,
read-result oracle, chosen schedule or atomic instruction assumption appears.

The primary geometry definitions preserve the source's modular low-32-bit
sign-extension, shift by seven, actual AUIPC PC and signed ADDI immediate.
The six arithmetic state updates yield mycpuRet under the explicit actual
AUIPC-PC premise. The linked literal cpus address and all eight valid-hart
specializations are ordinary Lean kernel proofs. No scalar WP assumes that
actual TP equals the hart index. Establishing and retaining that invariant is
part of the later function capability.

Validation: MycpuScalarLink passes 502 jobs; the explicit execution proof takes
1.3 seconds and geometry 3.4 seconds on the local build. The independent full
source and opaque/type/constructor audit is recorded in
../../docs/reviews/mycpu-scalar-peer-review.md (repository docs/reviews).
All computation certificates use ordinary kernel equality, without native_decide
or bv_decide. Definitional equality certificates use a Meta tactic only to
construct the equality proof term, which the kernel checks normally.

This is an execute-body prerequisite. It proves neither fetch/translation,
nextPC preparation, retirement, clock/restart, stack ownership, callee-saved
return composition nor the source MYCPU function WP. Its grouped geometry
state updates are not a claim that the physical machine skips the intervening
instruction cycles or memory instructions.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
