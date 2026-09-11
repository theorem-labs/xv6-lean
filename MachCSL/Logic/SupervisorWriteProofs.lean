import MachCSL.Logic.SupervisorWriteSpec
import MachCSL.Logic.SupervisorWritePlan
import MachCSL.Logic.TsoContextWriteWPLink
import MachCSL.Logic.TsoContextWordLink

namespace MachCSL.Logic.SupervisorWrite
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions TsoContextReadWP

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique, footprint]

theorem request_present (address word : BitVec 64) : (request address word).value = some word := rfl

theorem request_normal (address word : BitVec 64) :
    (request address word).access_kind = .AK_explicit { variety := .AV_plain, strength := .AS_normal } := rfl

theorem request_ram (address word : BitVec 64) (range : SupervisorPhysical.RamRange address 8) :
    deviceAddress (request address word).pa = false := SupervisorPhysical.device_ram address 8 range

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- Each prefix event is folded natively. At the actual write, the implemented
context rule pays the full heap/TSO update and handles blocked retries itself. -/
theorem Boundary.fold {A : Type} (fp : RegisterFootprint.Footprint)
    (unique : RegisterFootprint.Unique fp) (rs : RegisterFile)
    (req : MemoryWriteWP.WriteRequest 8) (program : SailM A)
    (tail : MemoryWriteWP.WriteResult → SailM A) (cut : Boundary fp rs req program tail)
    (old new : BitVec 64) (present : req.value = some new)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false)
    image fixed whole gen era cpu ξ rr (continuation : A → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
        running capacity era cpu ξ -∗ wordPointsto capacity era ξ req.pa (.own 1) new -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole
          (.hart gen cpu (tail (.Ok none) >>= continuation)) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction cut with
  | @event tail =>
    change iprop(⊢ _ -∗ _ -∗ _ -∗ _ -∗ _ -∗ _ -∗ MemoryWriteWP.threadWP capacity image fixed whole
      (.hart gen cpu (.impure (.writeMem 8 req)
        (fun response : MemoryWriteWP.WriteResult => (tail response >>= continuation : SailM Unit)))) post)
    iintro #Hcert Hregs Hrun Hword Hresv Hfinish
    iapply TsoContextWriteWP.wp_write capacity image fixed whole gen era cpu ξ req old new
      (fun response => tail response >>= continuation) rr post present ram plain
      $$ Hcert Hrun Hword Hresv
    iintro !> %view Hrun Hword Hresv Hreceipt
    iapply Hfinish $$ %view Hregs Hrun Hword Hresv Hreceipt
  | @«prefix» B segment value next tail before rest ih =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hrun Hword Hresv Hfinish
    iapply RegisterPlan.fold capacity fp unique image fixed whole gen era cpu rs segment
      (fun result after => result = value ∧ after = rs)
      (fun result => next result >>= continuation) post before $$ Hcert Hregs
    iintro %result %after %same Hregs
    rcases same with ⟨rfl, rfl⟩
    iapply ih $$ Hcert Hregs Hrun Hword Hresv Hfinish

/-- No access implementation is supplied by the caller: the concrete register
prefix and ordinary context-write rule discharge the actual checked store. -/
theorem wp_checked_write (shares : Shares) (rs : RegisterFile) (address : BitVec 64)
    (config : Machine.SupervisorPmp.TorRam rs) (range : SupervisorPhysical.RamRange address 8)
    (disabled : rs .htif_tohost_base = none) (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).writable = true)
    image fixed whole gen era cpu ξ (old new : BitVec 64) rr
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      running capacity era cpu ξ -∗ wordPointsto capacity era ξ address (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        running capacity era cpu ξ -∗ wordPointsto capacity era ξ address (.own 1) new -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok true))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address new >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hword Hresv Hfinish
  ihave %aligned := TsoContextWord.aligned (contextCapacity capacity) (contextNames era)
    ξ address (.own 1) old $$ Hword
  obtain ⟨tail, cut, success, _error⟩ := checked_boundary shares rs address new config range disabled
    region matched grant ((TsoContextWord.aligned_iff_sail address).mp aligned)
  have gate := Boundary.fold capacity (footprint shares) (footprint_unique shares) rs (request address new)
    (program address new) tail cut old new rfl (request_ram address new range) (by rfl)
    image fixed whole gen era cpu ξ rr continuation post
  rw [show (request address new).pa = address from rfl] at gate
  iapply gate $$ Hcert Hregs Hrun Hword Hresv
  iintro !> %view Hregs Hrun Hword Hresv Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view Hregs Hrun Hword Hresv Hreceipt

theorem actual : Spec capacity := ⟨wp_checked_write capacity⟩

end MachCSL.Logic.SupervisorWrite
