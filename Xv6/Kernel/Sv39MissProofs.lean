import Xv6.Kernel.Sv39MissRules

namespace Xv6.Kernel.Sv39Miss
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- Assemble the unchanged upper slots and actual A/D resources after the
native fill (or unchanged-TLB error branch). -/
theorem wp_finish shares rs asid path vpn permission cachedA cachedD physical branch
    image fixed whole gen era cpu bound dq values rr view2 view1 view0
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs [(.tlb, .own 1)] -∗
      TsoPinnedReadWP.credential capacity era cpu bound -∗
      Sv39Walk.slot capacity era path vpn permission bound dq values 2 -∗
      Sv39Walk.slot capacity era path vpn permission bound dq values 1 -∗
      Sv39Walk.receipts capacity era cpu view2 view1 view0 -∗
      (resources capacity era cpu rs shares asid path vpn permission
          (KptLeaf.word path.leaf permission cachedA cachedD) physical bound dq values rr
          view2 view1 view0 branch -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (result path.leaf branch))) post) -∗
      SupervisorPteAD.clientResources capacity era cpu rs shares (Sv39Walk.address path vpn 0)
        physical (KptLeaf.word path.leaf permission false false) bound rr branch -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (afterUpdate asid vpn (Sv39Walk.output path vpn permission false cachedA cachedD)
          (SupervisorPteAD.result physical branch) >>= continuation)) post) := by
  iintro #Hcert Htlb Hcred Hslot2 Hslot1 Hwalk Hfinish Had
  iunfold SupervisorPteAD.clientResources at Had
  icases Had with ⟨Hregs, Hslot0, Hresv, Hreceipt, Hcanon⟩
  ihave Hregs := (cells_ad capacity era cpu rs shares).mpr $$ [Hregs Htlb]
  · iframe Hregs Htlb
  iapply wp_after_update capacity shares rs asid path vpn permission cachedA cachedD physical branch
    image fixed whole gen era cpu continuation post $$ Hcert Hregs
  iintro Hregs
  iapply Hfinish $$ [Hregs Hcred Hslot2 Hslot1 Hslot0 Hresv Hwalk Hreceipt Hcanon]
  iunfold resources
  iunfold slots
  iframe Hregs Hcred Hslot2 Hslot1 Hslot0 Hresv Hwalk Hreceipt Hcanon

theorem wp_miss shares rs asid path vpn regions (config : Config rs path vpn regions)
    permission a d access (supported : KptLeaf.Supported access) (allowed : KptLeaf.Allows permission access)
    mxr doSum image fixed whole gen era cpu bound dq values rr
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoPinnedReadWP.credential capacity era cpu bound -∗
      slots capacity era path vpn permission (KptLeaf.word path.leaf permission a d) bound dq values -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ ▷ ▷ (∀ cachedA cachedD view2 view1 view0 branch,
        ⌜SupervisorPteAD.BranchFacts (KptLeaf.word path.leaf permission cachedA cachedD)
          (KptLeaf.word path.leaf permission a d) access (SupervisorPteAD.enabled rs) branch⌝ -∗
        SupervisorPteAD.guarded branch iprop(
          resources capacity era cpu rs shares asid path vpn permission
            (KptLeaf.word path.leaf permission cachedA cachedD) (KptLeaf.word path.leaf permission a d)
            bound dq values rr view2 view1 view0 branch -∗
          MemoryReadWP.threadWP capacity image fixed whole
            (.hart gen cpu (continuation (result path.leaf branch))) post)) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program asid path vpn access mxr doSum >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  rw [program_eq, BootPmp.sail_bind_assoc]
  iintro #Hcert Hregs Hcred Hslots Hresv Hfinish
  ihave ⟨Hregs, Hrest⟩ := (cells_walk capacity era cpu rs shares).mp $$ Hregs
  isimp only [slots_walk] at Hslots
  iapply Sv39Walk.wp_walk capacity shares.memory rs path vpn regions config.walk
    permission access supported allowed mxr doSum false image fixed whole gen era cpu bound
    (walkDq dq) (walkValues values (KptLeaf.word path.leaf permission a d)) rr
    (fun walked => afterWalk asid vpn access mxr doSum walked >>= continuation) post
    $$ Hcert Hregs Hcred Hslots Hresv
  iintro !> !> !> %cachedA %cachedD %view2 %view1 %view0 Hregs Hcred Hslots Hresv Hwalk
  ihave Hregs := (cells_walk capacity era cpu rs shares).mpr $$ [Hregs Hrest]
  · iframe Hregs Hrest
  ihave ⟨Hregs, Htlb⟩ := (cells_ad capacity era cpu rs shares).mp $$ Hregs
  isimp only [← slots_walk] at Hslots
  iunfold slots at Hslots
  icases Hslots with ⟨Hslot2, Hslot1, Hslot0⟩
  isimp only [after_walk, BootPmp.sail_bind_assoc]
  iapply SupervisorPteAD.wp_update capacity shares rs (Sv39Walk.address path vpn 0) (regions 0)
    config.update path.leaf permission a d cachedA cachedD vpn access supported allowed mxr doSum
    image fixed whole gen era cpu bound rr
    (fun updated => afterUpdate asid vpn (Sv39Walk.output path vpn permission false cachedA cachedD)
      updated >>= continuation) post $$ Hcert Hregs Hslot0 Hresv
  iunfold SupervisorPteAD.finish
  iintro %branch %facts
  ihave Hfinish := Hfinish $$ %cachedA %cachedD %view2 %view1 %view0 %branch %facts
  cases branch <;> simp only [SupervisorPteAD.guarded]
  all_goals first | iintro !> !> | iintro !> | skip
  all_goals
    iapply wp_finish capacity shares rs asid path vpn permission cachedA cachedD
      (KptLeaf.word path.leaf permission a d) _ image fixed whole gen era cpu bound dq values rr
      view2 view1 view0 continuation post $$ Hcert Htlb Hcred Hslot2 Hslot1 Hwalk Hfinish

theorem actual : Spec capacity := ⟨wp_miss capacity⟩
end Xv6.Kernel.Sv39Miss
