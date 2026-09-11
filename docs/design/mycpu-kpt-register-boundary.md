# Mycpu register bodies on the shared-KPT packet

This completed adapter is the first bounded layer toward all fourteen
decoded instruction bodies. It covers the nine scalar bodies and the final compressed return;
`MycpuKptMemory` already supplies the four memory bodies. It does not claim
fetch, retirement, cycle composition, full sconf or the complete function.

The source is pinned at `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, and the
generated model at `23dcf8fd923eb8a1958795393d2975632aa940b2`. I read the full
existing MycpuScalar proofs and actual MycpuReturn plan, plus the source
frame setup and caller completion at `ProofMycpu.v:90–150,270–318`.

## Actual programs and ownership

`Instruction.scalar i` selects source image indices 0/3/4/5/6/7/8/9/12.
`Instruction.returns` selects index13. `body` is the actual generated
`execute (MycpuDecode.decoded index)` followed by its single ExecuteAs
selection, exactly the existing scalar and return bodies. The public proof
reuses the existing six-cell scalar and five-cell return RegisterPlans,
widening them to the fifty owned keys without adding reads or writes.

The only register packet is `MycpuRegimeShell.resources (.kpt N root)`:
18 control cells, full mstatus and all31 physical GPRs, with native
SIE/SRET/off fragments and the software x0 fact. SATP/TLB/PMPcfg/PMPaddr stay
solely inside the folded native KPT residue. Scalar bodies require no
hardware-value premise. Return retains the existing exact owned Supervisor,
MENVCFG.LPE=false and MISA.C=1 assumptions; RA and old nextPC are arbitrary.
The actual return reads old nextPC even though the link destination is x0,
clears RA bit0 and performs the real nextPC write.

Each scalar instruction changes one explicitly identified typed GPR:
SP, S0, a5 or a0. `scalarIndex` and `scalarRegister` use explicit mappings,
with a checked physical correspondence obligation. `afterValues` updates
only that software index from the actual scalar post-state value.
`afterControl` is unchanged for scalar bodies and updates only nextPC for
return. The proof establishes exact complete entry-overlay equality,
x0/TP preservation, unchanged mstatus and physical PC, and the actual plan.
No unowned synthetic TLB or register projection becomes an ownership claim.

## Fixed save-area frame

The native WP carries an arbitrary literal IProp frame unchanged. It can
contain running context, reservation fragments, timer capability, text,
stack remainder and virtual save words at a fixed address. It does not
reindex those words when the actual SP push/pop modifies the register map.

A later all-fourteen family must name the save-area anchor explicitly,
normally entrySP−16. Memory bodies require actual SP equal to that anchor;
scalar bodies preserve the anchored words while changing SP. The original
source performs the same distinction when it allocates the frame before
saving RA/S0 and joins the frame after restoring them. A current-SP pair
cannot simply be rewritten to the new-SP pair across a scalar instruction.

## Proved contracts

`PureSpec` has thirteen fields: two actual-body identities, typed physical
index and nonzero/non-TP facts, two exact entry-overlay equalities, other-GPR
and x0/TP preservation, unchanged mstatus/PC, actual return target, and the
full register-event plan for all ten bodies. `Spec.body` requires the actual
packet and literal frame and returns the updated packet/frame to a genuine
Retire_Success continuation. There is no per-instruction body WP, memory
success assertion or software preservation callback among its premises.

The native implementation splits Shell.partition, uses the actual
RegisterPlan.fold, retains the bit frame and residue, and reassembles the
same fifty-cell source packet with the proved software-map/control result.
No new camera or frozen dependency was changed. `nativePureSpec` and
`nativeSpec` construct all thirteen pure and one native contract;
`registrySpec` reuses the existing canonical capacities.

The final five-module build passed 890 jobs (Pure 10 s, Proofs 1.0 s,
Link 901 ms). A fresh physical-origin audit checked all 118 declarations and
complete types, opaque bodies and constructors. Only propext, Classical.choice
and Quot.sound occur, with no unsafe/partial dependency and zero exclusions.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
