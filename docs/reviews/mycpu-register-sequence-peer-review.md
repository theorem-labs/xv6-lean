# Independent mycpu register-sequence review

Reviewed by the OpenAI Codex `lean_logic_audit` subagent, independently of
the coordinator who implemented this slice. **PASS for the stated pure
bookkeeping scope.** No code correction was requested or made.

I read all four `Xv6/Kernel/MycpuRegisterSequence{Defs,Spec,Proofs,Link}.lean`
modules and STATUS, the reused Scalar/Memory/Return post-state definitions,
and the exact source register chain and return proof in
`ProofMycpu.v:73–95,248–318`, `CalleeSaved.v:34–47`, and
`ProcGeom.v:772–785`. Source pin:
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The expressions retain the eleven actual GPR updates in their source order:
SP decrement, S0 frame pointer, three A5 updates, three A0 updates, restored
RA, restored S0, and SP increment. The explicit PC assignment supplies the
linked AUIPC address at decoded index 7; it is documented as an input to
later cycle composition. It is not a claim that these expressions model
all intervening PC, timer, retirement, reservation, or memory changes.

The two load post-states explicitly use entry RA and S0. The theorems do
not claim that RAM returns those values: native stack ownership and actual
load rules must establish that separately. Modular subtraction/addition
restores arbitrary SP without a no-wrap premise. The thirteen source ABI
registers, additional saved RA, actual JR low-bit-cleared nextPC, and full
modular `mycpuRet(entryTP)` are proved. TP is not silently replaced by a
hart constant, and is not added to the source callee-saved relation.

Fresh validation rebuilt the target successfully (**525 jobs**) and audited
all **55 physical-origin declarations** in the four modules, including
private helpers. Dependency traversal includes types, opaque theorem bodies
via `value? (allowOpaque := true)`, and constructors. The complete logical
cones use only the standard permitted axioms, with no unsafe/partial
declarations and **zero exclusions**. The public Spec is constructed from
these checked theorems. This is not a fetched function WP or a source KPT
translation theorem.

Evidence outside the repository:
`/tmp/xv6-lean-research/MycpuRegisterSequencePeerAudit.lean`,
`mycpu-register-sequence-peer-build.log`, and
`mycpu-register-sequence-peer-audit.log` in the same directory.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
