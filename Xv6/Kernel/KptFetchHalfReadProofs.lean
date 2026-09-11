import Xv6.Kernel.KptFetchHalfPureProofs
import MachCSL.Logic.MemoryReadWPLink
import MachCSL.Logic.SupervisorFetchReadProofs

namespace Xv6.Kernel.KptFetchHalf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem pristine_fold {A : Type} (fp : RegisterFootprint.Footprint)
    (unique : RegisterFootprint.Unique fp) (rs : RegisterFile)
    (n : Nat) (req : MemoryReadWP.ReadRequest n) (body : SailM A)
    (tail : MemoryReadWP.ReadResult n → SailM A)
    (cut : SupervisorFetchRead.Boundary fp rs req body tail)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false)
    image fixed whole gen era cpu dq (word : BitVec (8*n))
    (continuation : A → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs fp -∗
      TsoRead.byteWindow capacity.machine.era.heap.ledger era.heap req.pa n dq word -∗
      TsoRead.pristineWindow capacity.machine.era.heap.ledger era.timestamps req.pa n -∗
      ▷ (∀ view, RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs fp -∗
        TsoRead.byteWindow capacity.machine.era.heap.ledger era.heap req.pa n dq word -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole
          (.hart gen cpu (tail (.Ok (word,none)) >>= continuation)) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (body >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity.machine fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction cut with
  | @event tail =>
    change iprop(⊢ _ -∗ _ -∗ _ -∗ _ -∗ _ -∗ MemoryReadWP.threadWP capacity.machine image fixed whole
      (.hart gen cpu (.impure (.readMem n req) (fun response : MemoryReadWP.ReadResult n => (tail response >>= continuation : SailM Unit)))) post)
    iintro #Hcert Hregs Hword Hpristine Hfinish
    have primitive := MemoryReadWP.wp_ram_read_pristine capacity.machine image fixed whole gen era cpu n req
      (fun response => tail response >>= continuation) dq word post ram plain
    ieval (change _ ⊢ MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (.impure (.readMem n req) (fun response : MemoryReadWP.ReadResult n => tail response >>= continuation))) post)
    iapply primitive $$ Hcert Hword Hpristine
    iintro !> %view Hword Hreceipt
    iapply Hfinish $$ %view Hregs Hword Hreceipt
  | @«prefix» B segment value next tail before rest ih =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hword Hpristine Hfinish
    iapply RegisterPlan.fold capacity.machine fp unique image fixed whole gen era cpu rs segment
      (fun result after => result = value ∧ after = rs)
      (fun result => next result >>= continuation) post before $$ Hcert Hregs
    iintro %result %after %same Hregs
    rcases same with ⟨rfl,rfl⟩
    iapply ih $$ Hcert Hregs Hword Hpristine Hfinish

theorem read_opened shares rs data (config : Config rs) address n (width : Supported n)
    (text : KernelTextDatum.AddrIsText address) (aligned : is_aligned_paddr (.Physaddr address) n = true)
    image fixed whole gen era cpu N root (word : BitVec (8*n))
    (continuation : _root_.Sail.Result (BitVec (8*n)) (physaddr × ExceptionType) → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ KptAddress.opened capacity era cpu rs N root data -∗
      KernelTextDatum.physicalWindow capacity era address n .discard word -∗
      KernelTextDatum.pristineWindow capacity era address n -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗ KptResidue.residue capacity era cpu N root -∗
        Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity.machine image fixed whole (.hart gen cpu (continuation (.Ok word))) post) -∗
      MemoryReadWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr address) n false false false >>= continuation)) post) := by
  iintro #Hcert Haux Hopened Hbytes Hpristine Hfinish
  iunfold KptAddress.opened at Hopened
  icases Hopened with ⟨Hdata,%rooted,Hsnapshot,%tor,Hshared,Hcred⟩
  ihave Hcells := (KptAddress.partition capacity era cpu rs shares data).mpr $$ [Haux Hdata]
  · iframe Haux Hdata
  obtain ⟨tail,cut,success,_⟩ := physical_read shares rs data config tor address n width text aligned
  have gate := pristine_fold capacity (KptAddress.footprint shares) (KptAddress.unique shares)
    (KptAddress.prepare rs data) n (SupervisorFetchRead.request address n) _ tail cut
    (SupervisorPhysical.device_ram address n (text_range address n width text)) (by rfl)
    image fixed whole gen era cpu .discard word continuation post
  simp only [SupervisorFetchRead.request] at gate
  iunfold KptAddress.cells at Hcells
  iapply gate $$ Hcert Hcells Hbytes Hpristine
  iintro !> %view Hcells Hbytes Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  ihave Hcells' : KptAddress.cells capacity era cpu (KptAddress.prepare rs data) shares $$ [Hcells]
  · unfold KptAddress.cells; iexact Hcells
  ihave ⟨Haux,Hdata⟩ := (KptAddress.partition capacity era cpu rs shares data).mp $$ Hcells'
  iapply Hfinish $$ %view Haux [Hdata Hsnapshot Hshared Hcred] Hreceipt
  iapply KptAddress.close_residue capacity era cpu rs N root data
  iunfold KptAddress.opened
  iframe Hdata Hsnapshot Hshared Hcred
  isplit
  · ipureintro; exact rooted
  · ipureintro; exact tor

end Xv6.Kernel.KptFetchHalf
