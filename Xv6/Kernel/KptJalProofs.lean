import Xv6.Kernel.KptJalActiveProofs

namespace Xv6.Kernel.KptJal
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem wp_cycle shares control values (config : Config control) pc imm (atPC : control .PC = pc)
    (even : TargetEven pc imm) tier ξ rr tick image fixed whole gen era cpu (N : Namespace) root (frame : IProp GF) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗ code capacity era tier pc imm -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      cycleFinish capacity image fixed whole gen era cpu shares control values N root tier ξ pc imm frame post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post) := by
  iintro #Hcert Hpacket #Hcode Hrun Hresv Hframe Hfinish
  iapply (MycpuRegimeShell.nativeSpec capacity).start shares control values (.kpt N root) config.active tick
    image fixed whole gen era cpu
    (iprop(TsoContextReadWP.running capacity.machine era cpu ξ ∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr ∗ frame)) post
    $$ Hcert Hpacket [Hrun Hresv Hframe]
  · iframe
  · iintro Hpacket ⟨Hrun,Hresv,Hframe⟩
    isimp only [MycpuRegimeShell.active]
    iapply wp_active capacity shares (started control) values (MycpuKptCycle.started_config control config) pc imm atPC even
      tier ξ rr image fixed whole gen era cpu N root frame (MycpuRegimeShell.finish tick) post
      $$ Hcert Hpacket Hcode Hrun Hresv Hframe
    iunfold activeFinish
    iunfold cycleFinish at Hfinish
    iunfold guards
    iunfold guards at Hfinish
    iapply KptFetch.guardChunks_mono $$ [] Hfinish
    iintro %trace Hfinish Hresources
    iunfold activeResources at Hresources
    icases Hresources with ⟨Hpacket,_,Hrun,Hresv,Hreceipts,Hframe⟩
    iapply (MycpuRegimeShell.nativeSpec capacity).restart shares (afterControl pc imm (started control))
      (afterValues pc values) (.kpt N root)
      (after_config pc imm (started control) (MycpuKptCycle.started_config control config)).active
      tick (encoding imm) image fixed whole gen era cpu (KptFetchHalf.traceReservation rr trace)
      (iprop(TsoContextReadWP.running capacity.machine era cpu ξ ∗
        KptFetchHalf.receipts capacity.translation era cpu trace ∗ frame)) post $$ Hcert Hpacket [Hrun Hreceipts Hframe] Hresv
    · iframe
    · iintro %after %done
      ihave Hnext := Hfinish $$ %after %done
      iintro !> %nextTick Hpacket ⟨Hrun,Hreceipts,Hframe⟩ Hresv
      iapply Hnext $$ %nextTick [Hpacket Hrun Hreceipts Hframe Hresv]
      iunfold cycleResources
      iframe Hpacket Hcode Hrun Hreceipts Hframe Hresv

theorem actual : Spec capacity := ⟨wp_fetch capacity,wp_body capacity,wp_active capacity,wp_cycle capacity⟩

end Xv6.Kernel.KptJal
