import Xv6.Kernel.KptADSpec
import Xv6.Kernel.KptExclusiveEventLink
import MachCSL.Logic.SupervisorPteReadLink
import MachCSL.Logic.SupervisorPteADProofs

namespace Xv6.Kernel.KptAD
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

private theorem fold_read {A : Type} (fp : RegisterFootprint.Footprint)
    (unique : RegisterFootprint.Unique fp) (rs : RegisterFile)
    (req : MemoryReadWP.ReadRequest 8) (program : SailM A) (tail : MemoryReadWP.ReadResult 8 → SailM A)
    (cut : SupervisorRead.Boundary fp rs req program tail)
    (ram : deviceAddress req.pa = false) (exclusive : accessExclusive req.access_kind = true)
    image fixed whole gen era cpu (N : Namespace) root tree vpn p2 p1 p0
    (mapped : PtTree.Maps tree vpn p2 p1 p0) (location : req.pa = PtTree.addr0 p1 vpn)
    rr (continuation : A → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs fp -∗
      clients capacity era N root tree -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view word, ⌜PteCanonical.canon word = PteCanonical.canon p0⌝ -∗
        RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs fp -∗
        clients capacity era N root tree -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
          (some (snapshot req.pa 8 word)) -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (tail (.Ok (word, none)) >>= continuation)) post) -∗
      MemoryWriteWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction cut with
  | @event tail =>
    change iprop(⊢ _ -∗ _ -∗ _ -∗ _ -∗ _ -∗ MemoryWriteWP.threadWP capacity.machine image fixed whole
      (.hart gen cpu (.impure (.readMem 8 req)
        (fun response : MemoryReadWP.ReadResult 8 => (tail response >>= continuation : SailM Unit)))) post)
    iintro #Hcert Hregs Hclients Hresv Hfinish
    have event := (KptExclusiveEvent.nativeSpec capacity).read image fixed whole gen era cpu N root tree vpn p2 p1 p0
      mapped req location ram exclusive rr (fun response => tail response >>= continuation) post
    rw [show KptExclusiveEvent.clients capacity era N root tree = clients capacity era N root tree from rfl] at event
    iapply event $$ Hcert Hclients Hresv
    iintro !> %view %word %canonical Hclients Hresv Hview
    iapply Hfinish $$ %view %word %canonical Hregs Hclients Hresv Hview
  | @«prefix» B segment value next tail before rest ih =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hclients Hresv Hfinish
    iapply RegisterPlan.fold capacity.machine fp unique image fixed whole gen era cpu rs segment
      (fun result after => result = value ∧ after = rs)
      (fun result => next result >>= continuation) post before $$ Hcert Hregs
    iintro %result %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    iapply ih $$ Hcert Hregs Hclients Hresv Hfinish

/-- Five owned controls are restored around the real exclusive PTE wrapper;
its physical result is selected by the shared event, not supplied upfront. -/
theorem wp_read shares rs address region (config : SupervisorPteRead.Config rs address region)
    image fixed whole gen era cpu (N : Namespace) root tree vpn p2 p1 p0
    (mapped : PtTree.Maps tree vpn p2 p1 p0) (location : address = PtTree.addr0 p1 vpn)
    rr (continuation : SupervisorPteRead.Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era N root tree -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view observed, ⌜PteCanonical.canon observed = PteCanonical.canon p0⌝ -∗
        cells capacity era cpu rs shares -∗ clients capacity era N root tree -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu
          (some (snapshot address 8 observed)) -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok observed))) post) -∗
      MemoryWriteWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (read_pte_exclusive (.Physaddr address) 8 >>= continuation)) post) := by
  iintro #Hcert Hregs Hclients Hresv Hfinish
  ihave ⟨Hregs,Henv⟩ := (SupervisorPteAD.cells_split capacity.machine era cpu rs shares).mp $$ Hregs
  obtain ⟨tail,cut,success,_error⟩ := SupervisorPteRead.program_boundary shares.memory rs true address region config
  have gate := fold_read capacity (SupervisorPteRead.footprint shares.memory)
    (SupervisorRead.footprint_unique shares.memory) rs (SupervisorPteRead.request true address)
    (SupervisorPteRead.program true address) tail cut (SupervisorPhysical.device_ram address 8 config.range)
    (by rfl) image fixed whole gen era cpu N root tree vpn p2 p1 p0 mapped location rr continuation post
  rw [show (SupervisorPteRead.request true address).pa = address from rfl, SupervisorPteRead.actual_exclusive] at gate
  iapply gate $$ Hcert Hregs Hclients Hresv
  iintro !> %view %observed %canonical Hregs Hclients Hresv Hview
  rw [success, BootPmp.sail_pure_bind]
  ihave Hregs := (SupervisorPteAD.cells_split capacity.machine era cpu rs shares).mpr $$ [Hregs Henv]
  · iframe Hregs Henv
  iapply Hfinish $$ %view %observed %canonical Hregs Hclients Hresv Hview

end Xv6.Kernel.KptAD
