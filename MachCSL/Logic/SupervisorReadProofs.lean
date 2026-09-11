import MachCSL.Logic.SupervisorReadSpec
import MachCSL.Logic.SupervisorReadPlan
import MachCSL.Logic.TsoContextReadWPLink

namespace MachCSL.Logic.SupervisorRead
open Iris Iris.BI MachCSL.Machine LeanPaperStock.Functions

theorem footprint_unique (shares : Shares) : RegisterFootprint.Unique (footprint shares) := by
  simp [RegisterFootprint.Unique, footprint]

theorem alignment (address : BitVec 64) (aligned : TsoContextWord.Aligned address) :
    is_aligned_paddr (.Physaddr address) 8 = true := by
  unfold is_aligned_paddr _root_.Sail.BitVec.toNatInt
  change ((Int.tmod (address.toNat : Int) 8) == 0) = true
  have same : Int.tmod (address.toNat : Int) 8 = ((address.toNat % 8 : Nat) : Int) := by
    rfl
  rw [same, aligned]
  rfl

variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF)

/-- Structural folding of a finite register prefix into one actual owned read.
The residual is retained for all V1 responses; the native rule chooses success. -/
theorem Boundary.fold {A : Type} (fp : RegisterFootprint.Footprint)
    (unique : RegisterFootprint.Unique fp) (rs : RegisterFile)
    (req : MemoryReadWP.ReadRequest 8) (program : SailM A)
    (tail : MemoryReadWP.ReadResult 8 → SailM A)
    (cut : Boundary fp rs req program tail)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false)
    image fixed whole gen era cpu ξ dq (word : BitVec 64)
    (continuation : A → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
      TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextReadWP.wordPointsto capacity era ξ req.pa dq word -∗
      ▷ (∀ view, RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs fp -∗
        TsoContextReadWP.running capacity era cpu ξ -∗
        TsoContextReadWP.wordPointsto capacity era ξ req.pa dq word -∗
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
      (.hart gen cpu (.impure (.readMem 8 req) (fun response : MemoryReadWP.ReadResult 8 => (tail response >>= continuation : SailM Unit)))) post)
    iintro #Hcert Hregs Hrun Hword Hfinish
    iapply TsoContextReadWP.wp_read capacity image fixed whole gen era cpu ξ req
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

theorem wp_checked_read (shares : Shares) (rs : RegisterFile) (kind : Kind)
    (address : BitVec 64) (config : Machine.SupervisorPmp.TorRam rs)
    (range : SupervisorPhysical.RamRange address 8) (disabled : rs .htif_tohost_base = none)
    (region : PMA_Region)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr address) 8 = some region)
    (grant : SupervisorPhysical.ReadGrant (override_PMA region.attributes .PBMT_PMA) (access kind))
    image fixed whole gen era cpu ξ dq (word : BitVec 64)
    (continuation : Result → SailM Unit) post :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs shares -∗
      TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextReadWP.wordPointsto capacity era ξ address dq word -∗
      ▷ (∀ view, cells capacity era cpu rs shares -∗
        TsoContextReadWP.running capacity era cpu ξ -∗
        TsoContextReadWP.wordPointsto capacity era ξ address dq word -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryReadWP.threadWP capacity image fixed whole
          (.hart gen cpu (continuation (.Ok (word, ())))) post) -∗
      MemoryReadWP.threadWP capacity image fixed whole
        (.hart gen cpu (program kind address >>= continuation)) post) := by
  iintro #Hcert Hregs Hrun Hword Hfinish
  ihave %aligned := TsoContextWord.aligned (TsoContextReadWP.contextCapacity capacity)
    (TsoContextReadWP.contextNames era) ξ address dq word $$ Hword
  obtain ⟨tail, cut, success, _error⟩ := checked_boundary shares rs kind address config range
    disabled region matched grant (alignment address aligned)
  have gate := Boundary.fold capacity (footprint shares) (footprint_unique shares) rs (request address)
    (program kind address) tail cut (SupervisorPhysical.device_ram address 8 range) (by rfl)
    image fixed whole gen era cpu ξ dq word continuation post
  rw [show (request address).pa = address from rfl] at gate
  iapply gate $$ Hcert Hregs Hrun Hword
  iintro !> %view Hregs Hrun Hword Hreceipt
  rw [success, BootPmp.sail_pure_bind]
  iapply Hfinish $$ %view Hregs Hrun Hword Hreceipt

theorem actual : Spec capacity := ⟨wp_checked_read capacity⟩

end MachCSL.Logic.SupervisorRead
