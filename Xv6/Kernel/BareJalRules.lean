import Xv6.Kernel.BareJalResources
namespace Xv6.Kernel.BareJal
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

omit [Platform] in
theorem fetch_config control cpu values (config : Config control) satp pmp
    (mode : _get_Satp64_Mode (Mk_Satp64 satp) = 0#4) (tor : SupervisorPmp.TorRam pmp)
    (facts : SupervisorBits.MsFacts (control .mstatus)) :
    BareJalFetch.Config (entry (patch control satp pmp) cpu values) := by
  refine ⟨⟨config.privilege,facts.2.1,mode⟩,?_,config.pma,config.htif,?_⟩
  · exact ⟨tor.tor,tor.positive,tor.execute,tor.write,tor.read,tor.covers⟩
  · change _get_Misa_C (control .misa) = 1#1
    rw [config.misa]; rfl

theorem wp_fetch control values (config : Config control) pc imm (atPC : control .PC = pc)
    ξ rr image fixed whole gen era cpu (frame : IProp GF) continuation post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu control values -∗ code capacity era pc imm -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      fetchFinish capacity image fixed whole gen era cpu ξ control values pc imm rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (fetch () >>= continuation)) post) := by
  iintro #Hcert Hpacket #Hcode Hrun Hresv Hframe Hfinish
  ihave ⟨%satp,%pmp,%mode,%tor,Hcells,Hsaved⟩ := (partition capacity era cpu control values).mp $$ Hpacket
  iunfold fetchFrame at Hsaved
  icases Hsaved with ⟨Hrest,Hbits,Hz⟩
  iunfold MycpuRegimeShell.bitFrame at Hbits
  icases Hbits with ⟨Hsie,Hsret,%facts,Hoff⟩
  ihave Hsaved : fetchFrame capacity era cpu (patch control satp pmp) values $$ [Hrest Hsie Hsret Hoff Hz]
  · iunfold fetchFrame
    iunfold MycpuRegimeShell.bitFrame
    iframe Hrest Hsie Hsret Hoff Hz
    ipureintro; exact facts
  have entryPC : entry (patch control satp pmp) cpu values .PC = pc := atPC
  ihave Hinstr : BareJalFetch.code capacity.translation era (entry (patch control satp pmp) cpu values .PC) (encoding imm) $$ []
  · rw [entryPC]; iunfold code at Hcode; iunfold KptJal.code at Hcode
    iunfold BareJalFetch.code
    isimp only [KptJal.result] at Hcode
    iexact Hcode
  ieval (change _ ⊢ RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (BareJalFetch.program >>= continuation)) post)
  iapply BareJalFetch.wp_fetch capacity.translation fetchShares (entry (patch control satp pmp) cpu values)
    (fetch_config control cpu values config satp pmp mode tor facts) (encoding imm)
    image fixed whole gen era cpu ξ continuation post $$ Hcert Hcells Hrun Hinstr
  iunfold BareJalFetch.finish
  rw [entryPC]
  iunfold fetchFinish at Hfinish
  iapply BareJalFetch.guards_mono $$ [Hsaved Hresv Hframe] Hfinish
  iintro %views Hdone Hresources
  iunfold BareJalFetch.resources at Hresources
  icases Hresources with ⟨Hcells,Hrun,_,Hreceipts⟩
  ihave Hpacket := (partition capacity era cpu control values).mpr $$ [Hcells Hsaved]
  · iexists satp,pmp
    iframe
    isplitr
    · ipureintro; exact mode
    ipureintro; exact tor
  isimp only [result,KptJal.result] at Hdone
  iapply Hdone
  iunfold fetchResources
  iframe Hpacket Hcode Hrun Hresv Hreceipts Hframe

theorem wp_body control values (config : Config control) pc imm (atPC : control .PC = pc)
    (atNext : control .nextPC = KptJal.link pc) (even : TargetEven pc imm)
    ξ image fixed whole gen era cpu (frame : IProp GF)
    (continuation : ExecutionResult → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu control values -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗ frame -∗
      (bodyResources capacity era cpu ξ control values pc imm frame -∗
        RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (.Retire_Success ()))) post) -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (body imm >>= continuation)) post) := by
  iintro Hcert Hpacket Hrun Hframe Hfinish
  iunfold packet at Hpacket
  ihave ⟨Hcells,Hbits,Hz,Htr⟩ := (MycpuRegimeShell.partition capacity era cpu .bare control values shares).mp $$ Hpacket
  iapply RegisterPlan.fold capacity.machine (MycpuRegimeShell.footprint shares) (MycpuRegimeShell.footprint_unique shares)
    image fixed whole gen era cpu (entry control cpu values) _ _ continuation post
    (KptJal.body_plan shares control cpu values pc imm config atPC atNext even) $$ Hcert Hcells
  iintro %result %after %done Hcells
  rcases done with ⟨rfl,rfl⟩
  ihave Hpacket := (MycpuRegimeShell.partition capacity era cpu .bare
    (afterControl pc imm control) (afterValues pc values) shares).mpr $$ [Hcells Hbits Hz Htr]
  · isimp only [afterValues,KptJal.zero]
    isimp only [show afterControl pc imm control .mstatus = control .mstatus from rfl]
    iframe
  iapply Hfinish
  iunfold bodyResources
  iunfold packet
  iframe

end Xv6.Kernel.BareJal
