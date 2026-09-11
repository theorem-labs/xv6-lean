import Xv6.Kernel.BareJalPrefixProofs

namespace Xv6.Kernel.BareJal
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem wp_active control values (config : Config control) pc imm (atPC : control .PC = pc)
    (even : TargetEven pc imm) ξ rr image fixed whole gen era cpu
    (frame : IProp GF) (continuation : Step → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu control values -∗ code capacity era pc imm -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      activeFinish capacity image fixed whole gen era cpu ξ control values pc imm rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (run_hart_active 0 >>= continuation)) post) := by
  iintro #Hcert Hpacket #Hcode Hrun Hresv Hframe Hfinish
  ihave %aligned : ⌜is_aligned_vaddr (.Virtaddr pc) 2 = true⌝ $$ []
  · iunfold code at Hcode; iapply KptJal.alignment capacity era .identity pc imm $$ Hcode
  have encodable := KptJal.immediate_even pc imm aligned even
  iunfold packet at Hpacket
  ihave %disabled := (MycpuRegimeShell.nativeSpec capacity).disabled era cpu .bare control values shares $$ Hpacket
  ihave Hpacket' : packet capacity era cpu control values $$ [Hpacket]
  · iunfold packet; iexact Hpacket
  iapply wp_prefix capacity control control values cpu rfl _ _
    (MycpuKptCycle.dispatch_prefix shares control cpu values config disabled.1)
    image fixed whole gen era
    (iprop(TsoContextReadWP.running capacity.machine era cpu ξ ∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr ∗ frame)) continuation post
    $$ Hcert Hpacket' [Hrun Hresv Hframe]
  · iframe
  · iintro Hpacket ⟨Hrun,Hresv,Hframe⟩
    rw [BootPmp.sail_bind_assoc]
    iapply wp_fetch capacity control values config pc imm atPC ξ rr image fixed whole gen era cpu frame
      (fun fetched => MycpuActive.afterFetch 0 fetched >>= continuation) post $$ Hcert Hpacket Hcode Hrun Hresv Hframe
    iunfold fetchFinish
    iunfold activeFinish at Hfinish
    iapply BareJalFetch.guards_mono $$ [] Hfinish
    iintro %trace Hdone Hresources
    iunfold fetchResources at Hresources
    icases Hresources with ⟨Hpacket,_,Hrun,Hresv,Hreceipts,Hframe⟩
    iapply wp_prefix capacity control (prepared pc control) values cpu rfl _ _
      (KptJal.prepare_plan shares control cpu values pc imm config atPC encodable)
      image fixed whole gen era
      (iprop(TsoContextReadWP.running capacity.machine era cpu ξ ∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr ∗
        BareJalFetch.receipts capacity.translation era cpu trace ∗ frame)) continuation post
      $$ Hcert Hpacket [Hrun Hresv Hreceipts Hframe]
    · iframe
    · iintro Hpacket ⟨Hrun,Hresv,Hreceipts,Hframe⟩
      isimp only [KptJal.executeTail,BootPmp.sail_bind_assoc,BootPmp.sail_pure_bind]
      iapply wp_body capacity (prepared pc control) values (KptJal.prepared_config pc control config) pc imm atPC rfl even
        ξ image fixed whole gen era cpu
        (iprop(Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr ∗
          BareJalFetch.receipts capacity.translation era cpu trace ∗ frame))
        (fun execution => continuation (.Step_Execute (execution,encoding imm))) post $$ Hcert Hpacket Hrun [Hresv Hreceipts Hframe]
      · iframe
      · iintro Hresources
        iunfold bodyResources at Hresources
        icases Hresources with ⟨Hpacket,Hrun,Hresv,Hreceipts,Hframe⟩
        isimp only [afterControl,prepared,KptJal.after_prepared] at Hpacket
        iapply Hdone
        iunfold activeResources
        iunfold fetchResources
        iframe Hpacket Hcode Hrun Hresv Hreceipts Hframe

end Xv6.Kernel.BareJal
