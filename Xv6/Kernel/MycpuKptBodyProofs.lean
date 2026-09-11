import Xv6.Kernel.MycpuKptBodyPure
import Xv6.Kernel.MycpuKptRegisterLink
import Xv6.Kernel.MycpuKptMemoryLink

namespace Xv6.Kernel.MycpuKptBody
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

omit [Platform] in
theorem pair_eq era cpu tier ξ entrySP values words
    (sp : HartTp.rget cpu values 2#5 = anchor entrySP) :
    pair capacity era tier ξ entrySP words = MycpuKptMemory.pair capacity era cpu tier ξ values words := by
  simp only [pair, MycpuKptMemory.pair, MycpuKptMemory.address, slotAddress, sp]

theorem wp_body i shares control values (config : Config i control)
    entrySP tier ξ words rr image fixed whole gen era cpu (N : Namespace) root
    (ready : StackReady i entrySP cpu values) (frame : IProp GF)
    (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      pair capacity era tier ξ entrySP words -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu shares control values N root (route i)
        tier ξ entrySP words rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (MycpuKptBody.body i >>= continuation)) post) := by
  rw [body_route]
  cases h : route i with
  | registers instruction =>
    simp only [routedBody]
    simp only [Config, h] at config
    iintro Hcert Hpacket Hrun Hpair Hresv Hframe Hfinish
    let extra : IProp GF := iprop(TsoContextReadWP.running capacity.machine era cpu ξ ∗
      pair capacity era tier ξ entrySP words ∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr ∗ frame)
    iapply (MycpuKptRegister.nativeSpec capacity).body instruction shares control values config
      image fixed whole gen era cpu N root extra continuation post
      $$ Hcert Hpacket [Hrun Hpair Hresv Hframe] [Hfinish]
    · isimp only [extra]; iframe
    · iintro Hresources
      iunfold MycpuKptRegister.resources at Hresources
      icases Hresources with ⟨Hpacket,Hextra⟩
      isimp only [extra] at Hextra
      icases Hextra with ⟨Hrun,Hpair,Hresv,Hframe⟩
      iunfold finish at Hfinish
      iapply Hfinish
      iunfold resources
      isimp only [afterControl, afterValues, afterWords, afterReservation, receipts]
      iframe
  | memory kind slot =>
    simp only [routedBody]
    simp only [Config, h] at config
    simp only [StackReady, h] at ready
    iintro Hcert Hpacket Hrun Hpair Hresv Hframe Hfinish
    ihave Hpair := Hpair
    isimp only [pair_eq capacity era cpu tier ξ entrySP values words ready] at Hpair
    iapply (MycpuKptMemory.nativeSpec capacity).pair shares control values config kind slot tier ξ words rr
      image fixed whole gen era cpu N root frame continuation post
      $$ Hcert Hpacket Hrun Hpair Hresv Hframe [Hfinish]
    iunfold MycpuKptMemory.finishPair
    iapply MycpuKptMemory.guards_frame
      (P := fun ppn data translation => iprop(
        ⌜KptMemory.CompletedFacts (entry control cpu values) data root kind (slotAddress entrySP slot) ppn translation⌝ -∗
        ▷ (∀ view, resources capacity era cpu shares control values N root (.memory kind slot)
          tier ξ entrySP words rr (.memory kind slot translation view) frame -∗
          RegisterWP.threadWP capacity.machine image fixed whole
            (.hart gen cpu (continuation (.Retire_Success ()))) post)))
      (R := iprop(True)) (next := ?_) $$ [Hfinish]
    · intro ppn data outcome
      unfold MycpuKptMemory.continuePair
      iintro ⟨_,Hfinish⟩ %facts
      have address : MycpuKptMemory.address cpu values slot = slotAddress entrySP slot := by
        simp only [MycpuKptMemory.address, slotAddress, ready]
      rw [address] at facts
      ihave Hfinish := Hfinish $$ %facts
      iintro !> %view Hresources
      iunfold MycpuKptMemory.pairResources at Hresources
      icases Hresources with ⟨Hpacket,Hrun,Hpair,Hresv,Hreceipts,Hview,Hframe⟩
      isimp only [← pair_eq capacity era cpu tier ξ entrySP values _ ready] at Hpair
      isimp only [address] at Hresv Hreceipts
      iapply Hfinish $$ %view [Hpacket Hrun Hpair Hresv Hreceipts Hview Hframe]
      iunfold resources
      isimp only [afterControl, afterValues, afterWords, afterReservation, receipts]
      iframe
    · isplit
      · itrivial
      · isimp only [finish] at Hfinish
        iexact Hfinish

theorem actual : Spec capacity := ⟨wp_body capacity⟩

end Xv6.Kernel.MycpuKptBody
