import MachCSL.Logic.SupervisorPteWriteSpec
import MachCSL.Logic.SupervisorPteWritePlan
import MachCSL.Logic.TsoPinnedWriteWPLink

namespace MachCSL.Logic.SupervisorPteWrite
open Iris Iris.BI MachCSL.Machine MachCSL.Memory LeanPaperStock.Functions

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique, footprint, SupervisorWrite.footprint]

theorem request_ram (address word : BitVec 64) (range : SupervisorPhysical.RamRange address 8) :
    deviceAddress (request address word).pa = false := SupervisorPhysical.device_ram address 8 range

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- Fold every actual register prefix through the native fractional-register
rule, then pay the single real exclusive write with full pinned resources. -/
theorem fold_boundary {A : Type} (fp : RegisterFootprint.Footprint)
    (unique : RegisterFootprint.Unique fp) (rs : RegisterFile)
    (req : MemoryWriteWP.WriteRequest 8) (program : SailM A)
    (tail : MemoryWriteWP.WriteResult → SailM A)
    (cut : SupervisorWrite.Boundary fp rs req program tail)
    (reserved physical new : BitVec 64) (floors : Nat → Nat) (sets : Nat → Tso.ByteSet)
    (present : req.value = some new) (ram : deviceAddress req.pa = false)
    (exclusive : accessExclusive req.access_kind = true)
    (members : ∀ j, j < 8 → nthByte new j ∈ sets j)
    image fixed whole gen era cpu (continuation : A → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu
        (some (snapshot req.pa 8 reserved)) -∗
      TsoPinnedWriteWP.pinWindow capacity era req.pa physical (.own 1) floors sets -∗
      ▷ (∀ time, RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
        TsoPinnedWriteWP.storedWindow capacity era req.pa new time floors sets -∗
        Tso.History.logElem capacity.era.history era.logEntries (time - 1)
          ⟨snapshot req.pa 8 new, hartAgent cpu⟩ -∗ ⌜0 < time⌝ -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) time -∗
        MemoryWriteWP.threadWP capacity image fixed whole
          (.hart gen cpu (tail (.Ok none) >>= continuation)) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction cut with
  | @event tail =>
    change iprop(⊢ _ -∗ _ -∗ _ -∗ _ -∗ _ -∗ MemoryWriteWP.threadWP capacity image fixed whole
      (.hart gen cpu (.impure (.writeMem 8 req)
        (fun response : MemoryWriteWP.WriteResult => (tail response >>= continuation : SailM Unit)))) post)
    iintro #Hcert Hregs Hresv Hpin Hfinish
    iapply TsoPinnedWriteWP.wp_write capacity image fixed whole gen era cpu req reserved physical new
      floors sets (fun response => tail response >>= continuation) post present ram exclusive members
      $$ Hcert Hresv Hpin
    unfold TsoPinnedWriteWP.continuation
    iintro !> %time Hpin Hmessage %positive Hresv Hview
    iapply Hfinish $$ %time Hregs Hpin Hmessage [] Hresv Hview
    ipureintro; exact positive
  | @«prefix» B segment value next tail before rest ih =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hresv Hpin Hfinish
    iapply RegisterPlan.fold capacity fp unique image fixed whole gen era cpu rs segment
      (fun result after => result = value ∧ after = rs)
      (fun result => next result >>= continuation) post before $$ Hcert Hregs
    iintro %result %after %same Hregs
    rcases same with ⟨rfl, rfl⟩
    iapply ih $$ Hcert Hregs Hresv Hpin Hfinish

/-- The public wrapper supplies its actual checked prefix, byte payer and
reservation logic internally. Only the real final continuation is provided. -/
theorem wp_write (shares : Shares) (rs : RegisterFile) (address : BitVec 64) (region : PMA_Region)
    (config : Config rs address region) image fixed whole gen era cpu
    (reserved physical new : BitVec 64) floors sets (continuation : Result → SailM Unit) post
    (members : ∀ j, j < 8 → nthByte new j ∈ sets j) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu
        (some (snapshot address 8 reserved)) -∗
      TsoPinnedWriteWP.pinWindow capacity era address physical (.own 1) floors sets -∗
      ▷ (∀ time, cells capacity era cpu rs shares -∗
        TsoPinnedWriteWP.storedWindow capacity era address new time floors sets -∗
        Tso.History.logElem capacity.era.history era.logEntries (time - 1)
          ⟨snapshot address 8 new, hartAgent cpu⟩ -∗ ⌜0 < time⌝ -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) time -∗
        MemoryWriteWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok true))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (write_pte_conditional (.Physaddr address) 8 new >>= continuation)) post) := by
  iintro #Hcert Hregs Hresv Hpin Hfinish
  obtain ⟨tail, cut, success, _error⟩ := program_boundary shares rs address new region config
  have gate := fold_boundary capacity (footprint shares) (footprint_unique shares) rs (request address new)
    (write_pte_conditional (.Physaddr address) 8 new) tail cut reserved physical new floors sets
    rfl (request_ram address new config.range) rfl members image fixed whole gen era cpu continuation post
  rw [show (request address new).pa = address from rfl] at gate
  iapply gate $$ Hcert Hregs Hresv Hpin
  iintro !> %time Hregs Hpin Hmessage %positive Hresv Hview
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %time Hregs Hpin Hmessage [] Hresv Hview
  ipureintro; exact positive

theorem actual : Spec capacity := ⟨wp_write capacity⟩

end MachCSL.Logic.SupervisorPteWrite
