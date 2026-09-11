import MachCSL.Logic.SupervisorPteReadSpec
import MachCSL.Logic.SupervisorPteReadPlan
import MachCSL.Logic.TsoPinnedReadWPLink
import MachCSL.Logic.SupervisorReadProofs

namespace MachCSL.Logic.SupervisorPteRead
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

private theorem fold_plain {A : Type} (fp : RegisterFootprint.Footprint)
    (unique : RegisterFootprint.Unique fp) (rs : RegisterFile)
    (req : MemoryReadWP.ReadRequest 8) (program : SailM A) (tail : MemoryReadWP.ReadResult 8 → SailM A)
    (cut : SupervisorRead.Boundary fp rs req program tail)
    (ram : deviceAddress req.pa = false) (classified : accessExclusive req.access_kind = false)
    image fixed whole gen era cpu dq value bound (reference : BitVec 64) rr (continuation : A → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      TsoPinnedReadWP.credential capacity era cpu bound -∗
      TsoPinnedReadWP.slot capacity era req.pa 8 dq value bound (PteCanonical.slotSet reference) -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view word, ⌜PteCanonical.canon word = PteCanonical.canon reference⌝ -∗
        ⌜PteCanonical.nonleaf reference = true → word = reference⌝ -∗
        RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      TsoPinnedReadWP.credential capacity era cpu bound -∗
        TsoPinnedReadWP.slot capacity era req.pa 8 dq value bound (PteCanonical.slotSet reference) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (tail (.Ok (word, none)) >>= continuation)) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction cut with
  | @event tail =>
    change iprop(⊢ _ -∗ _ -∗ _ -∗ _ -∗ _ -∗ _ -∗ MemoryReadWP.threadWP capacity image fixed whole
      (.hart gen cpu (.impure (.readMem 8 req)
        (fun response : MemoryReadWP.ReadResult 8 => (tail response >>= continuation : SailM Unit)))) post)
    iintro #Hcert Hregs Hcred Hslot Hresv Hfinish
    iapply TsoPinnedReadWP.wp_pte (hlc := hlc) capacity image fixed whole gen era cpu req
      (fun response : MemoryReadWP.ReadResult 8 => (tail response >>= continuation : SailM Unit)) dq value bound reference rr post ram classified
      $$ Hcert Hcred Hslot Hresv
    iintro !> %view %word %canon %exactWord Hcred Hslot Hresv Hreceipt
    iapply Hfinish $$ %view %word [] [] Hregs Hcred Hslot Hresv Hreceipt
    · ipureintro; exact canon
    · ipureintro; exact exactWord
  | @«prefix» B segment result next tail before rest ih =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hcred Hslot Hresv Hfinish
    iapply RegisterPlan.fold capacity fp unique image fixed whole gen era cpu rs segment
      (fun value after => value = result ∧ after = rs)
      (fun value => next value >>= continuation) post before $$ Hcert Hregs
    iintro %value %after %same Hregs
    rcases same with ⟨rfl, rfl⟩
    iapply ih $$ Hcert Hregs Hcred Hslot Hresv Hfinish

private theorem fold_exclusive {A : Type} (fp : RegisterFootprint.Footprint)
    (unique : RegisterFootprint.Unique fp) (rs : RegisterFile)
    (req : MemoryReadWP.ReadRequest 8) (program : SailM A) (tail : MemoryReadWP.ReadResult 8 → SailM A)
    (cut : SupervisorRead.Boundary fp rs req program tail)
    (ram : deviceAddress req.pa = false) (classified : accessExclusive req.access_kind = true)
    image fixed whole gen era cpu dq (word : BitVec 64) bound sets rr (continuation : A → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      TsoPinnedReadWP.slot capacity era req.pa 8 dq (MachCSL.Memory.nthByte word) bound sets -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
        TsoPinnedReadWP.slot capacity era req.pa 8 dq (MachCSL.Memory.nthByte word) bound sets -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu (some (MachCSL.Memory.snapshot req.pa 8 word)) -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (tail (.Ok (word, none)) >>= continuation)) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction cut with
  | @event tail =>
    change iprop(⊢ _ -∗ _ -∗ _ -∗ _ -∗ _ -∗ MemoryReadWP.threadWP capacity image fixed whole
      (.hart gen cpu (.impure (.readMem 8 req)
        (fun response : MemoryReadWP.ReadResult 8 => (tail response >>= continuation : SailM Unit)))) post)
    iintro #Hcert Hregs Hslot Hresv Hfinish
    iapply TsoPinnedReadWP.wp_exclusive (hlc := hlc) capacity image fixed whole gen era cpu req
      (fun response : MemoryReadWP.ReadResult 8 => (tail response >>= continuation : SailM Unit)) dq word bound sets rr post ram classified
      $$ Hcert Hslot Hresv
    iintro !> %view Hslot Hresv Hreceipt
    iapply Hfinish $$ %view Hregs Hslot Hresv Hreceipt
  | @«prefix» B segment result next tail before rest ih =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hslot Hresv Hfinish
    iapply RegisterPlan.fold capacity fp unique image fixed whole gen era cpu rs segment
      (fun value after => value = result ∧ after = rs)
      (fun value => next value >>= continuation) post before $$ Hcert Hregs
    iintro %value %after %same Hregs
    rcases same with ⟨rfl, rfl⟩
    iapply ih $$ Hcert Hregs Hslot Hresv Hfinish

theorem wp_plain (shares : Shares) (rs : RegisterFile) (address : BitVec 64) (region : PMA_Region)
    (config : Config rs address region)
    image fixed whole gen era cpu dq value bound (reference : BitVec 64) rr
      (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      TsoPinnedReadWP.credential capacity era cpu bound -∗
      TsoPinnedReadWP.slot capacity era address 8 dq value bound (PteCanonical.slotSet reference) -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view word, ⌜PteCanonical.canon word = PteCanonical.canon reference⌝ -∗
        ⌜PteCanonical.nonleaf reference = true → word = reference⌝ -∗
        cells capacity era cpu rs shares -∗ TsoPinnedReadWP.credential capacity era cpu bound -∗
        TsoPinnedReadWP.slot capacity era address 8 dq value bound (PteCanonical.slotSet reference) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok word))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (read_pte (.Physaddr address) 8 >>= continuation)) post) := by
  iintro #Hcert Hregs Hcred Hslot Hresv Hfinish
  obtain ⟨tail, cut, success, _error⟩ := program_boundary shares rs false address region config
  have gate := fold_plain capacity (footprint shares) (SupervisorRead.footprint_unique shares) rs
    (request false address) (program false address) tail cut
    (SupervisorPhysical.device_ram address 8 config.range) (by rfl)
    image fixed whole gen era cpu dq value bound reference rr continuation post
  rw [show (request false address).pa = address from rfl] at gate
  rw [actual_plain] at gate
  iapply gate $$ Hcert Hregs Hcred Hslot Hresv
  iintro !> %view %word %canon %exactWord Hregs Hcred Hslot Hresv Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view %word [] [] Hregs Hcred Hslot Hresv Hreceipt
  · ipureintro; exact canon
  · ipureintro; exact exactWord

theorem wp_exclusive (shares : Shares) (rs : RegisterFile) (address : BitVec 64) (region : PMA_Region)
    (config : Config rs address region)
    image fixed whole gen era cpu dq (word : BitVec 64) bound sets rr
      (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗ cells capacity era cpu rs shares -∗
      TsoPinnedReadWP.slot capacity era address 8 dq (MachCSL.Memory.nthByte word) bound sets -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoPinnedReadWP.slot capacity era address 8 dq (MachCSL.Memory.nthByte word) bound sets -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu
          (some (MachCSL.Memory.snapshot address 8 word)) -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole (.hart gen cpu (continuation (.Ok word))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (read_pte_exclusive (.Physaddr address) 8 >>= continuation)) post) := by
  iintro #Hcert Hregs Hslot Hresv Hfinish
  obtain ⟨tail, cut, success, _error⟩ := program_boundary shares rs true address region config
  have gate := fold_exclusive capacity (footprint shares) (SupervisorRead.footprint_unique shares) rs
    (request true address) (program true address) tail cut
    (SupervisorPhysical.device_ram address 8 config.range) (by rfl)
    image fixed whole gen era cpu dq word bound sets rr continuation post
  rw [show (request true address).pa = address from rfl] at gate
  rw [actual_exclusive] at gate
  iapply gate $$ Hcert Hregs Hslot Hresv
  iintro !> %view Hregs Hslot Hresv Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view Hregs Hslot Hresv Hreceipt

theorem actual : Spec capacity := ⟨wp_plain capacity, wp_exclusive capacity⟩

end MachCSL.Logic.SupervisorPteRead
