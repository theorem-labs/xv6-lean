import MachCSL.Logic.SupervisorFetchReadSpec
import MachCSL.Logic.SupervisorFetchReadPlan
import MachCSL.Logic.TsoContextBytesReadWPLink

namespace MachCSL.Logic.SupervisorFetchRead
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique, footprint]

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- Structural folding of a finite register prefix into one actual owned read.
The residual is retained for all V1 responses; the native rule chooses success. -/
theorem Boundary.fold {A : Type} (fp : RegisterFootprint.Footprint)
    (unique : RegisterFootprint.Unique fp) (rs : RegisterFile)
    (n : Nat) (req : MemoryReadWP.ReadRequest n) (program : SailM A)
    (tail : MemoryReadWP.ReadResult n → SailM A)
    (cut : Boundary fp rs req program tail)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false)
    image fixed whole gen era cpu ξ dq (word : BitVec (8 * n))
    (continuation : A → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      TsoContextBytesReadWP.running capacity era cpu ξ -∗
      TsoContextBytesReadWP.window capacity era ξ req.pa n dq word -∗
      ▷ (∀ view, RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
        TsoContextBytesReadWP.running capacity era cpu ξ -∗
        TsoContextBytesReadWP.window capacity era ξ req.pa n dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (tail (.Ok (word, none)) >>= continuation)) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program >>= continuation)) post) := by
  haveI : Persistent (MachineInterp.generationCertificate capacity fixed gen era) := by
    unfold MachineInterp.generationCertificate PowerGhost.genStarted PowerGhost.genBorn Era.registered
    infer_instance
  induction cut with
  | @event tail =>
    change iprop(⊢ _ -∗ _ -∗ _ -∗ _ -∗ _ -∗ MemoryReadWP.threadWP capacity image fixed whole
      (.hart gen cpu (.impure (.readMem n req) (fun response : MemoryReadWP.ReadResult n => (tail response >>= continuation : SailM Unit)))) post)
    iintro #Hcert Hregs Hrun Hword Hfinish
    iapply TsoContextBytesReadWP.wp_read capacity image fixed whole gen era cpu ξ n req
      (fun response => tail response >>= continuation) dq word post ram plain $$ Hcert Hrun Hword
    iintro !> %view Hrun Hword Hreceipt
    iapply Hfinish $$ %view Hregs Hrun Hword Hreceipt
  | @«prefix» B segment value next tail before rest ih =>
    rw [BootPmp.sail_bind_assoc]
    iintro #Hcert Hregs Hrun Hword Hfinish
    iapply RegisterPlan.fold capacity fp unique image fixed whole gen era cpu rs segment
      (fun result after => result = value ∧ after = rs)
      (fun result => next result >>= continuation) post before $$ Hcert Hregs
    iintro %result %after %same Hregs
    rcases same with ⟨rfl, rfl⟩
    iapply ih $$ Hcert Hregs Hrun Hword Hfinish

theorem wp_checked_fetch (shares : Shares) (rs : RegisterFile)
    (address : BitVec 64) (n : Nat) (width : Supported n)
    (aligned : is_aligned_paddr (.Physaddr address) n = true) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address n) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) n = some region)
    (grant : (override_PMA region.attributes .PBMT_PMA).executable = true)
    image fixed whole gen era cpu ξ dq (word : BitVec (8 * n))
    (continuation : Result n → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoContextBytesReadWP.running capacity era cpu ξ -∗
      TsoContextBytesReadWP.window capacity era ξ address n dq word -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoContextBytesReadWP.running capacity era cpu ξ -∗
        TsoContextBytesReadWP.window capacity era ξ address n dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok (word, ())))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program address n >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hword Hfinish
  obtain ⟨tail, cut, success, _error⟩ := checked_boundary shares rs address n width config range
    disabled region matched grant aligned
  have gate := Boundary.fold capacity (footprint shares) (footprint_unique shares) rs n (request address n)
    (program address n) tail cut (SupervisorPhysical.device_ram address n range) (by rfl)
    image fixed whole gen era cpu ξ dq word continuation post
  rw [show (request address n).pa = address from rfl] at gate
  iapply gate $$ Hcert Hregs Hrun Hword
  iintro !> %view Hregs Hrun Hword Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view Hregs Hrun Hword Hreceipt

theorem actual : Spec capacity := ⟨wp_checked_fetch capacity⟩

end MachCSL.Logic.SupervisorFetchRead
