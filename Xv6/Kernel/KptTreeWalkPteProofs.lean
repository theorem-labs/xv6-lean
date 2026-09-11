import Xv6.Kernel.KptTreeWalkSpec
import Xv6.Kernel.KptReadEventLink
import MachCSL.Logic.SupervisorPteReadPlan
import MachCSL.Logic.RegisterPlanProofs
import MachCSL.Logic.SupervisorReadProofs

namespace Xv6.Kernel.KptTreeWalk
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

instance clients_persistent era cpu N root tree bound :
    Persistent (clients capacity era cpu N root tree bound) := by
  unfold clients
  infer_instance

/-- Induction over the checked register prefix, ending at the real shared
ordinary event. This internal fold is not a public read-success premise. -/
private theorem fold_boundary {A : Type} (fp : RegisterFootprint.Footprint)
    (unique : RegisterFootprint.Unique fp) (rs : RegisterFile)
    (tree : PtTree.Tree) vpn p2 p1 p0 (level : Fin 3)
    (mapped : PtTree.Maps tree vpn p2 p1 p0)
    (req : MemoryReadWP.ReadRequest 8)
    (location : req.pa = KptReadEvent.address tree vpn p2 p1 level)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false)
    (program : SailM A) (tail : MemoryReadWP.ReadResult 8 → SailM A)
    (cut : SupervisorRead.Boundary fp rs req program tail)
    image fixed whole gen era cpu (N : Namespace) root bound rr
    (continuation : A → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs fp -∗
      clients capacity era cpu N root tree bound -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view word, ⌜KptReadEvent.ReadFact (KptReadEvent.reference p2 p1 p0 level) word⌝ -∗
        RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs fp -∗
        clients capacity era cpu N root tree bound -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (tail (.Ok (word, none)) >>= continuation)) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction cut with
  | @event tail =>
    change iprop(⊢ _ -∗ _ -∗ _ -∗ _ -∗ _ -∗ MemoryReadWP.threadWP capacity.machine image fixed whole
      (.hart gen cpu (.impure (.readMem 8 req)
        (fun response : MemoryReadWP.ReadResult 8 => (tail response >>= continuation : SailM Unit)))) post)
    iintro #Hcert Hregs #Hclients Hresv Hfinish
    iunfold clients at Hclients
    icases Hclients with ⟨#Hshared,#Hsnapshot,#Hbound,#Hcred⟩
    iapply (KptReadEvent.nativeSpec capacity).read image fixed whole gen era cpu N root tree vpn p2 p1 p0 level
      mapped req location ram plain bound rr
      (fun response : MemoryReadWP.ReadResult 8 => (tail response >>= continuation : SailM Unit)) post
      $$ Hcert Hshared Hsnapshot Hbound Hcred Hresv
    iintro !> %view %word %relation Hshared Hsnapshot Hbound Hcred Hresv Hreceipt
    iapply Hfinish $$ %view %word %relation Hregs [Hshared Hsnapshot Hbound Hcred] Hresv Hreceipt
    iunfold clients
    iframe Hshared Hsnapshot Hbound Hcred
  | @«prefix» B segment result next tail before rest ih =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hclients Hresv Hfinish
    iapply RegisterPlan.fold capacity.machine fp unique image fixed whole gen era cpu rs segment
      (fun value after => value = result ∧ after = rs)
      (fun value => next value >>= continuation) post before $$ Hcert Hregs
    iintro %value %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    iapply ih $$ Hcert Hregs Hclients Hresv Hfinish

/-- The actual read_pte wrapper through one separately closed shared event. -/
theorem wp_pte shares rs tree vpn p2 p1 p0 (level : Fin 3)
    (mapped : PtTree.Maps tree vpn p2 p1 p0) region
    (config : SupervisorPteRead.Config rs (KptReadEvent.address tree vpn p2 p1 level) region)
    image fixed whole gen era cpu (N : Namespace) root bound rr
    (continuation : SupervisorPteRead.Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ clients capacity era cpu N root tree bound -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view word, ⌜KptReadEvent.ReadFact (KptReadEvent.reference p2 p1 p0 level) word⌝ -∗
        cells capacity era cpu rs shares -∗ clients capacity era cpu N root tree bound -∗
        Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (continuation (.Ok word))) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (read_pte (.Physaddr (KptReadEvent.address tree vpn p2 p1 level)) 8 >>= continuation)) post) := by
  iintro #Hcert Hregs Hclients Hresv Hfinish
  obtain ⟨tail,cut,success,_error⟩ := SupervisorPteRead.program_boundary shares rs false
    (KptReadEvent.address tree vpn p2 p1 level) region config
  have gate := fold_boundary capacity (SupervisorPteRead.footprint shares)
    (SupervisorRead.footprint_unique shares) rs tree vpn p2 p1 p0 level mapped
    (SupervisorPteRead.request false (KptReadEvent.address tree vpn p2 p1 level)) rfl
    (SupervisorPhysical.device_ram _ 8 config.range) rfl _ tail cut
    image fixed whole gen era cpu N root bound rr continuation post
  rw [SupervisorPteRead.actual_plain] at gate
  iapply gate $$ Hcert Hregs Hclients Hresv
  iintro !> %view %word %relation Hregs Hclients Hresv Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view %word %relation Hregs Hclients Hresv Hreceipt

end Xv6.Kernel.KptTreeWalk
