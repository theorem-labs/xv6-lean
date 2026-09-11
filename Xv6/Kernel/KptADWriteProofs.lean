import Xv6.Kernel.KptADSpec
import Xv6.Kernel.KptWriteEventLink
import MachCSL.Logic.SupervisorPteWriteLink
import MachCSL.Logic.SupervisorPteADProofs

namespace Xv6.Kernel.KptAD
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

private theorem fold_write {A : Type} (fp : RegisterFootprint.Footprint)
    (unique : RegisterFootprint.Unique fp) (rs : RegisterFile)
    (req : MemoryWriteWP.WriteRequest 8) (program : SailM A) (tail : MemoryWriteWP.WriteResult → SailM A)
    (cut : SupervisorWrite.Boundary fp rs req program tail) (reserved new : BitVec 64)
    (present : req.value = some new) (ram : deviceAddress req.pa = false)
    (exclusive : accessExclusive req.access_kind = true)
    image fixed whole gen era cpu (N : Namespace) root tree vpn p2 p1 p0
    (mapped : PtTree.Maps tree vpn p2 p1 p0) (location : req.pa = PtTree.addr0 p1 vpn)
    (canonical : PteCanonical.canon new = PteCanonical.canon p0)
    (continuation : A → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs fp -∗
      clients capacity era N root tree -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
        (some (snapshot req.pa 8 reserved)) -∗
      ▷ (∀ time, ⌜0 < time⌝ -∗
        RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs fp -∗
        clients capacity era N root tree -∗
        Tso.History.logElem capacity.machine.era.history era.logEntries (time - 1)
          ⟨snapshot req.pa 8 new, hartAgent cpu⟩ -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) time -∗
        MemoryWriteWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (tail (.Ok none) >>= continuation)) post) -∗
      MemoryWriteWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction cut with
  | @event tail =>
    change iprop(⊢ _ -∗ _ -∗ _ -∗ _ -∗ _ -∗ MemoryWriteWP.threadWP capacity.machine image fixed whole
      (.hart gen cpu (.impure (.writeMem 8 req)
        (fun response : MemoryWriteWP.WriteResult => (tail response >>= continuation : SailM Unit)))) post)
    iintro #Hcert Hregs Hclients Hresv Hfinish
    iapply (KptWriteEvent.nativeSpec capacity).write image fixed whole gen era cpu N root tree vpn p2 p1 p0
      mapped req reserved new location present ram exclusive canonical
      (fun response => tail response >>= continuation) post $$ Hcert Hclients Hresv
    iintro !> %time %positive Hclients Hmessage Hresv Hview
    iapply Hfinish $$ %time %positive Hregs Hclients Hmessage Hresv Hview
  | @«prefix» B segment value next tail before rest ih =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hclients Hresv Hfinish
    iapply RegisterPlan.fold capacity.machine fp unique image fixed whole gen era cpu rs segment
      (fun result after => result = value ∧ after = rs)
      (fun result => next result >>= continuation) post before $$ Hcert Hregs
    iintro %result %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    iapply ih $$ Hcert Hregs Hclients Hresv Hfinish

/-- The actual conditional wrapper reuses the complete checked prefix,
including both raw Boolean/error tails. Its successful native event pays the
shared update and returns every fractional control cell. -/
theorem wp_write shares rs address region (config : SupervisorPteWrite.Config rs address region)
    image fixed whole gen era cpu (N : Namespace) root tree vpn p2 p1 p0
    (mapped : PtTree.Maps tree vpn p2 p1 p0) (location : address = PtTree.addr0 p1 vpn)
    (reserved new : BitVec 64) (canonical : PteCanonical.canon new = PteCanonical.canon p0)
    (continuation : SupervisorPteWrite.Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era N root tree -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
        (some (snapshot address 8 reserved)) -∗
      ▷ (∀ time, ⌜0 < time⌝ -∗ cells capacity era cpu rs shares -∗
        clients capacity era N root tree -∗
        Tso.History.logElem capacity.machine.era.history era.logEntries (time - 1)
          ⟨snapshot address 8 new, hartAgent cpu⟩ -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) time -∗
        MemoryWriteWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok true))) post) -∗
      MemoryWriteWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (write_pte_conditional (.Physaddr address) 8 new >>= continuation)) post) := by
  iintro #Hcert Hregs Hclients Hresv Hfinish
  ihave ⟨Hregs,Henv⟩ := (SupervisorPteAD.cells_split capacity.machine era cpu rs shares).mp $$ Hregs
  let writeShares := SupervisorPteAD.writeShares shares
  obtain ⟨tail,cut,success,_error⟩ := SupervisorPteWrite.program_boundary writeShares rs address new region config
  have gate := fold_write capacity (SupervisorPteWrite.footprint writeShares)
    (SupervisorPteWrite.footprint_unique writeShares) rs (SupervisorPteWrite.request address new)
    (write_pte_conditional (.Physaddr address) 8 new) tail cut reserved new rfl
    (SupervisorPteWrite.request_ram address new config.range) rfl
    image fixed whole gen era cpu N root tree vpn p2 p1 p0 mapped location canonical continuation post
  rw [show (SupervisorPteWrite.request address new).pa = address from rfl] at gate
  rw [show SupervisorPteWrite.footprint writeShares = SupervisorPteRead.footprint shares.memory from rfl] at gate
  iapply gate $$ Hcert Hregs Hclients Hresv
  iintro !> %time %positive Hregs Hclients Hmessage Hresv Hview
  rw [success, BootPmp.sail_pure_bind]
  ihave Hregs := (SupervisorPteAD.cells_split capacity.machine era cpu rs shares).mpr $$ [Hregs Henv]
  · iframe Hregs Henv
  iapply Hfinish $$ %time %positive Hregs Hclients Hmessage Hresv Hview

end Xv6.Kernel.KptAD
