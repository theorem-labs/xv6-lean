import Xv6.Kernel.BareJalActiveProofs

namespace Xv6.Kernel.BareJal
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem wp_cycle control values (config : Config control) pc imm (atPC : control .PC = pc)
    (even : TargetEven pc imm) ξ rr tick image fixed whole gen era cpu (frame : IProp GF) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu control values -∗ code capacity era pc imm -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      cycleFinish capacity image fixed whole gen era cpu ξ control values pc imm frame post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post) := by
  iintro #Hcert Hpacket #Hcode Hrun Hresv Hframe Hfinish
  iunfold packet at Hpacket
  iapply (MycpuRegimeShell.nativeSpec capacity).start shares control values .bare config.active tick
    image fixed whole gen era cpu
    (iprop(TsoContextReadWP.running capacity.machine era cpu ξ ∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr ∗ frame)) post
    $$ Hcert Hpacket [Hrun Hresv Hframe]
  · iframe
  · iintro Hpacket ⟨Hrun,Hresv,Hframe⟩
    isimp only [MycpuRegimeShell.active]
    ihave Hpacket' : packet capacity era cpu (started control) values $$ [Hpacket]
    · iunfold packet; iexact Hpacket
    iapply wp_active capacity (started control) values (MycpuKptCycle.started_config control config) pc imm atPC even
      ξ rr image fixed whole gen era cpu frame (MycpuRegimeShell.finish tick) post
      $$ Hcert Hpacket' Hcode Hrun Hresv Hframe
    iunfold activeFinish
    iunfold cycleFinish at Hfinish
    iapply BareJalFetch.guards_mono $$ [] Hfinish
    iintro %trace Hfinish Hresources
    iunfold activeResources at Hresources
    iunfold fetchResources at Hresources
    icases Hresources with ⟨Hpacket,_,Hrun,Hresv,Hreceipts,Hframe⟩
    iunfold packet at Hpacket
    iapply (MycpuRegimeShell.nativeSpec capacity).restart shares (afterControl pc imm (started control))
      (afterValues pc values) .bare
      (KptJal.after_config pc imm (started control) (MycpuKptCycle.started_config control config)).active
      tick (encoding imm) image fixed whole gen era cpu rr
      (iprop(TsoContextReadWP.running capacity.machine era cpu ξ ∗
        BareJalFetch.receipts capacity.translation era cpu trace ∗ frame)) post $$ Hcert Hpacket [Hrun Hreceipts Hframe] Hresv
    · iframe
    · iintro %after %done
      ihave Hnext := Hfinish $$ %after %done
      iintro !> %nextTick Hpacket ⟨Hrun,Hreceipts,Hframe⟩ Hresv
      iapply Hnext $$ %nextTick [Hpacket Hrun Hreceipts Hframe Hresv]
      iunfold cycleResources
      iunfold fetchResources
      iunfold packet
      iframe Hpacket Hcode Hrun Hreceipts Hframe Hresv

theorem actual : Spec capacity := ⟨wp_fetch capacity,wp_body capacity,wp_active capacity,wp_cycle capacity⟩

end Xv6.Kernel.BareJal
