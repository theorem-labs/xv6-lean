import Xv6.Kernel.KptJalPrepareProofs
import Xv6.Kernel.KptJalResources

namespace Xv6.Kernel.KptJal
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem wp_active shares control values (config : Config control) pc imm (atPC : control .PC = pc)
    (even : TargetEven pc imm) tier ξ rr image fixed whole gen era cpu (N : Namespace) root
    (frame : IProp GF) (continuation : Step → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗ code capacity era tier pc imm -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      activeFinish capacity image fixed whole gen era cpu shares control values N root tier ξ pc imm rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (run_hart_active 0 >>= continuation)) post) := by
  iintro #Hcert Hpacket #Hcode Hrun Hresv Hframe Hfinish
  ihave %aligned := alignment capacity era tier pc imm $$ Hcode
  have encodable := immediate_even pc imm aligned even
  ihave %disabled := (MycpuRegimeShell.nativeSpec capacity).disabled era cpu (.kpt N root) control values shares $$ Hpacket
  iapply MycpuKptCycle.wp_prefix capacity shares control control values cpu rfl _ _
    (MycpuKptCycle.dispatch_prefix shares control cpu values config disabled.1)
    image fixed whole gen era N root
    (iprop(TsoContextReadWP.running capacity.machine era cpu ξ ∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr ∗ frame)) continuation post
    $$ Hcert Hpacket [Hrun Hresv Hframe]
  · iframe
  · iintro Hpacket ⟨Hrun,Hresv,Hframe⟩
    rw [BootPmp.sail_bind_assoc]
    iapply wp_fetch capacity shares control values config pc imm atPC tier ξ rr image fixed whole gen era cpu N root frame
      (fun fetched => MycpuActive.afterFetch 0 fetched >>= continuation) post $$ Hcert Hpacket Hcode Hrun Hresv Hframe
    iunfold fetchFinish
    iunfold activeFinish at Hfinish
    iunfold guards
    iunfold guards at Hfinish
    iapply KptFetch.guardChunks_mono $$ [] Hfinish
    iintro %trace Hdone Hresources
    iunfold fetchResources at Hresources
    icases Hresources with ⟨Hpacket,_,Hrun,Hresv,Hreceipts,Hframe⟩
    iapply MycpuKptCycle.wp_prefix capacity shares control (prepared pc control) values cpu rfl _ _
      (prepare_plan shares control cpu values pc imm config atPC encodable)
      image fixed whole gen era N root
      (iprop(TsoContextReadWP.running capacity.machine era cpu ξ ∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu (KptFetchHalf.traceReservation rr trace) ∗
        KptFetchHalf.receipts capacity.translation era cpu trace ∗ frame)) continuation post
      $$ Hcert Hpacket [Hrun Hresv Hreceipts Hframe]
    · iframe
    · iintro Hpacket ⟨Hrun,Hresv,Hreceipts,Hframe⟩
      isimp only [executeTail,BootPmp.sail_bind_assoc,BootPmp.sail_pure_bind]
      iapply wp_body capacity shares (prepared pc control) values (prepared_config pc control config) pc imm atPC rfl even
        ξ image fixed whole gen era cpu N root
        (iprop(Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu (KptFetchHalf.traceReservation rr trace) ∗
          KptFetchHalf.receipts capacity.translation era cpu trace ∗ frame))
        (fun execution => continuation (.Step_Execute (execution,encoding imm))) post $$ Hcert Hpacket Hrun [Hresv Hreceipts Hframe]
      · iframe
      · iintro Hresources
        iunfold bodyResources at Hresources
        icases Hresources with ⟨Hpacket,Hrun,Hresv,Hreceipts,Hframe⟩
        isimp only [after_prepared] at Hpacket
        iapply Hdone
        iunfold activeResources
        iframe Hpacket Hcode Hrun Hresv Hreceipts Hframe

end Xv6.Kernel.KptJal
