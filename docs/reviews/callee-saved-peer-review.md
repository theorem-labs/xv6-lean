# Callee-saved register algebra independent review

Reviewer: OpenAI Codex subagent `/root/lean_logic_audit`, independent of the
coordinator author. **PASS** for the pure register-algebra scope. Read all
four frozen modules and the complete pinned `iris/CalleeSaved.v`; no code
correction requested. Source pin:
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`registers` has precisely the thirteen source callee-saved keys: x2, x8, x9,
x18 through x27. `preserved_iff` proves the exact thirteen-conjunct statement,
and `tp_not_saved` records the source's deliberate exclusion of x4/TP. RA,
caller-saved GPRs and control registers have no preservation conjunct. This
matches the source reason that a suspended thread may resume on another hart;
it does not add a TP equality to function postconditions.

Reflexivity, transitivity and `caller_write` have the correct direction and
exact disequality side condition. The write list is outermost first and uses
foldr, so its head wins when several entries name the same register.
`outerWrite` finds that head-most occurrence; its dependent cast is justified
by actual key equality. `applyWrites_lookup` proves this meaning for every
typed register and arbitrary values. The default on no occurrence is the old
register value, not zero. `Restores` is precisely the source outer-write
obligation: absent keys are unconstrained, while the visible last-in-time
write to every callee-saved key must equal its entry value. The proved iff
with `Preserved` rules out a weaker sufficient-only surrogate.

Using the actual total typed Sail RegisterFile, and extending writes to
control registers, is a useful explicit generalization of the source GPR map
algebra. It does not itself prove a finite-map/Rocq representation theorem,
actual instruction execution, register ownership or whole-function WP. The
source Ltac helpers and boolean index presentation are not additional semantic
premises of the Lean algebra. `nativeSpec` is a constructed pure specification;
it is not an Iris resource assertion or an adequacy theorem.

Independent target rebuild passed **149 jobs**. Fresh physical-origin audit
covers all **40 logical declarations in four modules**, with every transitive
type, opaque body (`allowOpaque := true`) and inductive constructor. Only the
allowed standard axioms occur; the principal write lookup/restoration/native
spec theorems use `propext` alone. The one excluded root is the compiler-generated
runtime companion `Xv6.Kernel.CalleeSaved.outerWrite._unsafe_rec`; its owner
is a safe total recursive definition. No unsafe/partial declaration occurs in
any logical dependency cone. This exclusion is not a namespace or library
blanket exemption. Evidence:
`/tmp/xv6-lean-research/CalleeSavedPeerAudit.lean`,
`callee-saved-peer-audit.log`, `callee-saved-peer-build.log`.
No production file was edited.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
