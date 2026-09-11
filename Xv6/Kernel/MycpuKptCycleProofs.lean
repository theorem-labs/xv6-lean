import Xv6.Kernel.MycpuKptCycleActiveProofs

namespace Xv6.Kernel.MycpuKptCycle
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem wp_cycle (bodySpec : MycpuKptBody.Spec capacity) shares control values (config : Config control) i
    (pc : control .PC = MycpuDecode.address i)
    entrySP tier ξ words rr tick image fixed whole gen era cpu (N : Namespace) root
    (stack : MycpuKptBody.StackReady i entrySP cpu values) (frame : IProp GF) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗ code capacity era tier -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗ pair capacity era tier ξ entrySP words -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      cycleFinish capacity image fixed whole gen era cpu shares control values N root i tier ξ entrySP words frame post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post) := by
  iintro #Hcert Hpacket #Hcode Hrun Hpair Hresv Hframe Hfinish
  iapply (MycpuRegimeShell.nativeSpec capacity).start shares control values (.kpt N root) config.active tick
    image fixed whole gen era cpu
    (iprop(TsoContextReadWP.running capacity.machine era cpu ξ ∗ pair capacity era tier ξ entrySP words ∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr ∗ frame)) post
    $$ Hcert Hpacket [Hrun Hpair Hresv Hframe]
  · iframe
  · iintro Hpacket ⟨Hrun,Hpair,Hresv,Hframe⟩
    isimp only [MycpuRegimeShell.active]
    iapply wp_active capacity bodySpec shares (started control) values (started_config control config) i pc
      entrySP tier ξ words rr image fixed whole gen era cpu N root stack frame (MycpuRegimeShell.finish tick) post
      $$ Hcert Hpacket Hcode Hrun Hpair Hresv Hframe
    iunfold activeFinish
    iunfold cycleFinish at Hfinish
    iapply guards_mono $$ [] Hfinish
    iintro %trace %outcome Hfinish Hresources
    iunfold activeResources at Hresources
    icases Hresources with ⟨Hpacket,_,Hrun,Hpair,Hresv,Hreceipts,Hframe⟩
    iapply (MycpuRegimeShell.nativeSpec capacity).restart shares (bodyControl i (started control) cpu values)
      (bodyValues i (started control) cpu values words) (.kpt N root)
      (body_config_stable i (started control) cpu values (started_config control config)).active
      tick (MycpuActive.instbits i) image fixed whole gen era cpu (afterReservation i entrySP rr trace outcome)
      (iprop(TsoContextReadWP.running capacity.machine era cpu ξ ∗
        pair capacity era tier ξ entrySP (bodyWords i cpu values words) ∗
        receipts capacity era cpu i entrySP trace outcome ∗ frame)) post $$ Hcert Hpacket [Hrun Hpair Hreceipts Hframe] Hresv
    · iframe
    · iintro %after %done
      ihave Hnext := Hfinish $$ %after %done
      iintro !> %nextTick Hpacket ⟨Hrun,Hpair,Hreceipts,Hframe⟩ Hresv
      iapply Hnext $$ %nextTick [Hpacket Hrun Hpair Hreceipts Hframe Hresv]
      iunfold cycleResources
      iframe Hpacket Hcode Hrun Hpair Hreceipts Hframe Hresv

theorem actual (bodySpec : MycpuKptBody.Spec capacity) : Spec capacity :=
  ⟨wp_active capacity bodySpec,wp_cycle capacity bodySpec⟩

end Xv6.Kernel.MycpuKptCycle
