import Xv6.Kernel.KptHitPure
import Xv6.Kernel.KptADSpec

namespace Xv6.Kernel.KptHit
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

private theorem widen {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM A} {Q : A → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

theorem resume_plan shares rs asid vpn p2 p1 ppn permission a d branch :
    RegisterPlan.Returns (footprint shares) rs
      (Sv39Hit.afterUpdate vpn (TlbCoherence.index vpn)
        (entry asid vpn p2 p1 (KptLeaf.word ppn permission a d)) (KptAD.result branch))
      (result ppn branch)
      (after rs vpn (entry asid vpn p2 p1 (KptLeaf.word ppn permission a d)) branch) := by
  have pbmt : PtTree.PbmtZero (entry asid vpn p2 p1 (KptLeaf.word ppn permission a d)).pte := by
    change _get_PTE_Ext_PBMT (ext_bits_of_PTE (KptLeaf.word ppn permission a d)) = 0#2
    rw [KptLeaf.word_ext]
    rfl
  have plan := widen (Sv39Hit.resume_plan shares.environment rs vpn (TlbCoherence.index vpn)
    (entry asid vpn p2 p1 (KptLeaf.word ppn permission a d)) (KptAD.result branch)
    (Sv39Tlb.index_bound vpn) pbmt) (large := footprint shares) (by
      intro cell member
      simp only [Sv39Hit.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        simp [footprint, Sv39Miss.footprint, SupervisorPteAD.footprint])
  rw [result_eq] at plan
  exact plan

variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem cells_ad era cpu rs shares :
    iprop(cells capacity era cpu rs shares ⊣⊢
      KptAD.cells capacity era cpu rs shares ∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs [(.tlb, .own 1)]) :=
  RegisterFootprint.cells_append capacity.machine.era.registers _ rs _ _

variable [Platform] {hlc : HasLC} [InvGS_gen hlc GF]

theorem wp_resume shares rs asid vpn p2 p1 ppn permission a d branch
    image fixed whole gen era cpu (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗
      (cells capacity era cpu
          (after rs vpn (entry asid vpn p2 p1 (KptLeaf.word ppn permission a d)) branch) shares -∗
        MemoryWriteWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (result ppn branch))) post) -∗
      MemoryWriteWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (Sv39Hit.afterUpdate vpn (TlbCoherence.index vpn)
          (entry asid vpn p2 p1 (KptLeaf.word ppn permission a d)) (KptAD.result branch) >>= continuation)) post) := by
  have unique : RegisterFootprint.Unique (footprint shares) := by
    simp [RegisterFootprint.Unique, footprint, Sv39Miss.footprint, SupervisorPteAD.footprint,
      SupervisorPteRead.footprint, SupervisorRead.footprint]
  unfold cells Sv39Miss.cells
  iintro #Hcert Hregs Hfinish
  iapply RegisterPlan.fold (hlc := hlc) capacity.machine (footprint shares) unique
    image fixed whole gen era cpu rs _
    (fun value afterRs => value = result ppn branch ∧
      afterRs = after rs vpn (entry asid vpn p2 p1 (KptLeaf.word ppn permission a d)) branch)
    continuation post (resume_plan shares rs asid vpn p2 p1 ppn permission a d branch) $$ Hcert Hregs
  iintro %value %afterRs %same Hregs
  rcases same with ⟨rfl,rfl⟩
  iapply Hfinish $$ Hregs

end Xv6.Kernel.KptHit
