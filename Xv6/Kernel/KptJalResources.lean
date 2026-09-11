import Xv6.Kernel.KptJalEncodingProofs
import Xv6.Kernel.KptJalPlanProofs

namespace Xv6.Kernel.KptJal
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance code_persistent era tier pc imm : Persistent (code capacity era tier pc imm) := by
  unfold code; infer_instance

theorem alignment era tier pc imm :
    iprop(code capacity era tier pc imm ⊢ ⌜is_aligned_vaddr (.Virtaddr pc) 2 = true⌝) := by
  unfold code KptFetch.instrBytes
  iintro ⟨H,_⟩
  iexact H

theorem window era tier pc imm (aligned : is_aligned_vaddr (.Virtaddr pc) 2 = true) :
    iprop(KernelTextDatum.window capacity.translation era tier pc 4 .discard (encoding imm) ⊢ code capacity era tier pc imm) := by
  iintro H
  iunfold code
  iunfold KptFetch.instrBytes
  isimp only [result]
  iframe H
  ipureintro
  exact ⟨aligned,base imm⟩

theorem nativeResourceSpec : ResourceSpec capacity := ⟨code_persistent capacity,alignment capacity,window capacity⟩

variable [Platform] {hlc : HasLC} [InvGS_gen hlc GF]

theorem wp_fetch shares control values (config : Config control) pc imm (atPC : control .PC = pc)
    tier ξ rr image fixed whole gen era cpu (N : Namespace) root (frame : IProp GF)
    (continuation : FetchResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗ code capacity era tier pc imm -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      fetchFinish capacity image fixed whole gen era cpu shares control values N root tier ξ pc imm rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (fetch () >>= continuation)) post) := by
  iintro #Hcert Hpacket #Hcode Hrun Hresv Hframe Hfinish
  ihave ⟨Hcells,Hsaved,Hresidue⟩ := (MycpuKptFetch.packet_partition capacity era cpu control values shares N root).mp $$ Hpacket
  iunfold MycpuKptFetch.packetFrame at Hsaved
  icases Hsaved with ⟨Hrest,Hbits,Hz⟩
  iunfold MycpuRegimeShell.bitFrame at Hbits
  icases Hbits with ⟨Hsie,Hsret,%facts,Hoff⟩
  ihave Hsaved : MycpuKptFetch.packetFrame capacity era cpu control values shares $$ [Hrest Hsie Hsret Hoff Hz]
  · iunfold MycpuKptFetch.packetFrame
    iunfold MycpuRegimeShell.bitFrame
    iframe Hrest Hsie Hsret Hoff Hz
    ipureintro; exact facts
  have entryPC : entry control cpu values .PC = pc := atPC
  ihave Hinstr : KptFetch.instrBytes capacity.translation era tier (entry control cpu values .PC) (result imm) $$ []
  · rw [entryPC]; iunfold code at Hcode; iexact Hcode
  ieval (change _ ⊢ MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (KptFetch.program >>= continuation)) post)
  iapply KptFetch.wp_fetch capacity.translation (MycpuKptFetch.fetchShares shares) (entry control cpu values)
    (MycpuKptFetch.configuration control cpu values (MycpuKptCycle.fetch_config control config) facts)
    tier (result imm) image fixed whole gen era cpu N root rr continuation post $$ Hcert Hcells Hresidue Hinstr Hresv
  iunfold KptFetch.finish
  rw [entryPC]
  iunfold fetchFinish at Hfinish
  iunfold guards at Hfinish
  iapply KptFetch.guardChunks_mono $$ [Hsaved Hrun Hframe] Hfinish
  iintro %trace Hdone Hresources
  iunfold KptFetch.resources at Hresources
  icases Hresources with ⟨Hcells,Hresidue,Hresv,Hreceipts,_⟩
  ihave Hpacket := (MycpuKptFetch.packet_partition capacity era cpu control values shares N root).mpr $$ [Hcells Hsaved Hresidue]
  · iframe
  iapply Hdone
  iunfold fetchResources
  iframe Hpacket Hcode Hrun Hresv Hreceipts Hframe

theorem wp_body shares control values (config : Config control) pc imm (atPC : control .PC = pc)
    (atNext : control .nextPC = link pc) (even : TargetEven pc imm)
    ξ image fixed whole gen era cpu (N : Namespace) root (frame : IProp GF)
    (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu (.kpt N root) control values shares -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗ frame -∗
      (bodyResources capacity era cpu shares control values N root ξ pc imm frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (body imm >>= continuation)) post) := by
  iintro Hcert Hpacket Hrun Hframe Hfinish
  ihave ⟨Hcells,Hbits,Hz,Htr⟩ := (MycpuRegimeShell.partition capacity era cpu (.kpt N root) control values shares).mp $$ Hpacket
  iapply RegisterPlan.fold capacity.machine (footprint shares) (MycpuRegimeShell.footprint_unique shares)
    image fixed whole gen era cpu (entry control cpu values) _ _ continuation post
    (body_plan shares control cpu values pc imm config atPC atNext even) $$ Hcert Hcells
  iintro %result %after %done Hcells
  rcases done with ⟨rfl,rfl⟩
  ihave Hpacket := (MycpuRegimeShell.partition capacity era cpu (.kpt N root)
    (afterControl pc imm control) (afterValues pc values) shares).mpr $$ [Hcells Hbits Hz Htr]
  · rw [zero]
    isimp only [show afterControl pc imm control .mstatus = control .mstatus from rfl]
    iframe
  iapply Hfinish
  iunfold bodyResources
  iframe

end Xv6.Kernel.KptJal
