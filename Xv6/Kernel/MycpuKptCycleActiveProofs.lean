import Xv6.Kernel.MycpuKptCycleResources
import Xv6.Kernel.MycpuKptBodySpec

namespace Xv6.Kernel.MycpuKptCycle
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem wp_active (bodySpec : MycpuKptBody.Spec capacity) shares control values (config : Config control) i
    (pc : control .PC = MycpuDecode.address i)
    entrySP tier ξ words rr image fixed whole gen era cpu (N : Namespace) root
    (stack : MycpuKptBody.StackReady i entrySP cpu values) (frame : IProp GF)
    (continuation : Step → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗ code capacity era tier -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗ pair capacity era tier ξ entrySP words -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      activeFinish capacity image fixed whole gen era cpu shares control values N root i tier ξ entrySP words rr
        frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (run_hart_active 0 >>= continuation)) post) := by
  iintro #Hcert Hpacket #Hcode Hrun Hpair Hresv Hframe Hfinish
  ihave %disabled := (MycpuRegimeShell.nativeSpec capacity).disabled era cpu (.kpt N root) control values shares $$ Hpacket
  iapply wp_prefix capacity shares control control values cpu rfl _ _
    (dispatch_prefix shares control cpu values config disabled.1) image fixed whole gen era N root
    (iprop(TsoContextReadWP.running capacity.machine era cpu ξ ∗ pair capacity era tier ξ entrySP words ∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr ∗ frame)) continuation post
    $$ Hcert Hpacket [Hrun Hpair Hresv Hframe]
  · iframe
  · iintro Hpacket ⟨Hrun,Hpair,Hresv,Hframe⟩
    rw [BootPmp.sail_bind_assoc]
    ieval (change _ ⊢ MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (MycpuKptFetch.program >>= fun result => MycpuActive.afterFetch 0 result >>= continuation)) post)
    iapply (MycpuKptFetch.nativeSpec capacity).fetch shares control values (fetch_config control config) i pc tier
      image fixed whole gen era cpu N root rr
      (iprop(TsoContextReadWP.running capacity.machine era cpu ξ ∗ pair capacity era tier ξ entrySP words ∗ frame))
      (fun result => MycpuActive.afterFetch 0 result >>= continuation) post $$ Hcert Hpacket Hcode Hresv [Hrun Hpair Hframe]
    · iframe
    · iunfold MycpuKptFetch.finish
      iunfold activeFinish at Hfinish
      iunfold guards at Hfinish
      iapply KptFetch.guardChunks_mono $$ [] Hfinish
      iintro %trace Hbody Hresources
      iunfold MycpuKptFetch.resources at Hresources
      icases Hresources with ⟨Hpacket,_,Hresv,Hfetch,Hrun,Hpair,Hframe⟩
      iapply wp_prefix capacity shares control (Prepared i control) values cpu rfl _ _
        (prepare_owned shares control cpu values i config) image fixed whole gen era N root
        (iprop(TsoContextReadWP.running capacity.machine era cpu ξ ∗ pair capacity era tier ξ entrySP words ∗
          Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu (KptFetchHalf.traceReservation rr trace) ∗
          KptFetchHalf.receipts capacity.translation era cpu trace ∗ frame)) continuation post
        $$ Hcert Hpacket [Hrun Hpair Hresv Hfetch Hframe]
      · iframe
      · iintro Hpacket ⟨Hrun,Hpair,Hresv,Hfetch,Hframe⟩
        rw [execute_tail, BootPmp.sail_bind_assoc]
        simp only [BootPmp.sail_pure_bind]
        iapply bodySpec.body i shares (Prepared i control) values (body_config i control config)
          entrySP tier ξ words (KptFetchHalf.traceReservation rr trace) image fixed whole gen era cpu N root stack
          (iprop(KptFetchHalf.receipts capacity.translation era cpu trace ∗ frame))
          (fun result => continuation (.Step_Execute (result,MycpuActive.instbits i))) post
          $$ Hcert Hpacket Hrun Hpair Hresv [Hfetch Hframe]
        · iframe
        · rw [body_finish_eq]
          iapply bodyGuards_mono $$ [] Hbody
          iintro %outcome Hdone Hresources
          iunfold MycpuKptBody.resources at Hresources
          icases Hresources with ⟨Hpacket,Hrun,Hpair,Hresv,Hreceipts,Hfetch,Hframe⟩
          iapply Hdone
          iunfold activeResources
          iunfold receipts
          isimp only [bodyControl,bodyValues,bodyWords,afterReservation]
          iframe Hpacket Hcode Hrun Hpair Hresv Hreceipts Hfetch Hframe

end Xv6.Kernel.MycpuKptCycle
