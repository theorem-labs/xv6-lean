import Xv6.Kernel.Sv39MissFactor
import Xv6.Kernel.Sv39TlbLink
import Xv6.Kernel.Sv39WalkLink
import MachCSL.Logic.SupervisorPteADLink

namespace Xv6.Kernel.Sv39Miss
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

omit [Platform] in
theorem cells_ad era cpu rs shares :
    iprop(cells capacity era cpu rs shares ⊣⊢
      SupervisorPteAD.cells capacity era cpu rs shares ∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs [(.tlb, .own 1)]) :=
  RegisterFootprint.cells_append capacity.era.registers _ rs _ _

omit [Platform] in
theorem cells_walk era cpu rs shares :
    iprop(cells capacity era cpu rs shares ⊣⊢
      SupervisorPteRead.cells capacity era cpu rs shares.memory ∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs
        [(.menvcfg, shares.environment), (.tlb, .own 1)]) := by
  have eq : footprint shares = SupervisorPteRead.footprint shares.memory ++
      [(.menvcfg, shares.environment), (.tlb, .own 1)] := by
    simp [footprint, SupervisorPteAD.footprint, List.append_assoc]
  unfold cells
  rw [eq]
  exact RegisterFootprint.cells_append capacity.era.registers _ rs _ _

omit [Platform] in
private theorem widen {small large : RegisterFootprint.Footprint} {rs : RegisterFile}
    {program : SailM A} {Q : A → RegisterFile → Prop}
    (plan : RegisterPlan.Plan small rs program Q)
    (members : ∀ cell, cell ∈ small → cell ∈ large) : RegisterPlan.Plan large rs program Q := by
  induction plan with
  | pure good => exact .pure good
  | read member _ ih => exact .read (members _ member) ih
  | readAny _ ih => exact .readAny ih
  | write member _ ih => exact .write (members _ member) ih

/-- Native TLB fill on the same complete six-cell bundle. -/
theorem wp_fill shares rs asid vpn ppn pte address global
    image fixed whole gen era cpu (continuation : Unit → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      (cells capacity era cpu (Sv39Tlb.after rs asid vpn ppn pte address global) shares -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation ())) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (add_to_TLB 39 asid vpn ppn pte address 0 global >>= continuation)) post) := by
  have plan := widen (Sv39Tlb.fill_plan rs asid vpn ppn pte address global)
    (large := footprint shares) (by
      intro cell member
      simp only [Sv39Tlb.footprint, List.mem_cons, List.not_mem_nil, or_false] at member
      subst cell
      simp [footprint])
  have unique : RegisterFootprint.Unique (footprint shares) := by
    simp [RegisterFootprint.Unique, footprint, SupervisorPteAD.footprint,
      SupervisorPteRead.footprint, SupervisorRead.footprint]
  unfold cells
  iintro #Hcert Hregs Hfinish
  iapply RegisterPlan.fold (hlc := hlc) capacity (footprint shares) unique image fixed whole gen era cpu rs
    (add_to_TLB 39 asid vpn ppn pte address 0 global)
    (fun value after => value = () ∧ after = Sv39Tlb.after rs asid vpn ppn pte address global)
    continuation post plan $$ Hcert Hregs
  iintro %value %after %same Hregs
  rcases same with ⟨rfl, rfl⟩
  iapply Hfinish $$ Hregs

/-- The error path leaves the TLB unchanged; every successful branch fills
with the exact cached, reread or written word. -/
theorem wp_after_update shares rs asid path vpn permission cachedA cachedD physical branch
    image fixed whole gen era cpu (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      (cells capacity era cpu (after rs asid path vpn
          (KptLeaf.word path.leaf permission cachedA cachedD) physical branch) shares -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (result path.leaf branch))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (afterUpdate asid vpn (Sv39Walk.output path vpn permission false cachedA cachedD)
          (SupervisorPteAD.result physical branch) >>= continuation)) post) := by
  rw [after_update]
  cases branch <;> simp only [after, fillWord, BootPmp.sail_bind_assoc, BootPmp.sail_pure_bind]
  all_goals iintro #Hcert Hregs Hfinish
  all_goals first
  | iapply Hfinish $$ Hregs
  | iapply wp_fill capacity shares rs asid vpn path.leaf _ (.Physaddr (Sv39Walk.address path vpn 0)) false
      image fixed whole gen era cpu (fun _ => continuation (result path.leaf _)) post $$ Hcert Hregs Hfinish

omit [Platform] in
theorem slots_walk era path vpn permission physical bound dq values :
    slots capacity era path vpn permission physical bound dq values =
      Sv39Walk.slots capacity era path vpn permission bound (walkDq dq) (walkValues values physical) := by
  simp [slots, Sv39Walk.slots, Sv39Walk.slot, walkDq, walkValues, Sv39Walk.reference]

end Xv6.Kernel.Sv39Miss
