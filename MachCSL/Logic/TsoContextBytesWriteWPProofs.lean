import MachCSL.Logic.TsoContextBytesWriteWPSpec
import MachCSL.Logic.TsoContextBytesStoreLink
import MachCSL.Logic.MemoryWriteWPLink

namespace MachCSL.Logic.TsoContextBytesWriteWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContextBytesReadWP

theorem ordinary_view (g : State) (cpu : CPU) (req : MemoryWriteWP.WriteRequest n)
    (plain : accessExclusive req.access_kind = false) :
    MemoryWriteWP.postView g cpu req = g.views cpu := by
  simp [MemoryWriteWP.postView, plain]

/-- Ordinary writes retain every CPU view; only exclusive writes take the
post-log view. This is an equation of the actual event successor. -/
theorem write_views (g : State) (cpu : CPU) (req : MemoryWriteWP.WriteRequest n)
    (word : BitVec (8 * n)) (plain : accessExclusive req.access_kind = false) :
    (MemoryWriteWP.writeState g cpu req word).views = g.views := by
  funext other
  by_cases same : other = cpu
  · subst other
    simp [MemoryWriteWP.writeState, MemoryWriteWP.postView, updateHart, plain]
  · simp [MemoryWriteWP.writeState, MemoryWriteWP.postView, updateHart, same]

theorem write_effect (g : State) (cpu : CPU) (req : MemoryWriteWP.WriteRequest n)
    (word : BitVec (8 * n)) (plain : accessExclusive req.access_kind = false) :
    Effect g (MemoryWriteWP.writeState g cpu req word) cpu req word :=
  ⟨rfl, rfl, write_views g cpu req word plain, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The exact functional write state is the registered finite-map store's
successor; no caller-supplied successor correspondence is assumed. -/
theorem write_transition (g : State) (cpu : CPU) (req : MemoryWriteWP.WriteRequest n)
    (word : BitVec (8 * n)) (plain : accessExclusive req.access_kind = false) :
    TsoContextStore.OrdinaryTransition g (MemoryWriteWP.writeState g cpu req word)
      (TsoStore.windowMap req.pa n word) cpu := by
  refine ⟨rfl, ?_, ?_, write_views g cpu req word plain⟩
  · simp only [MemoryWriteWP.writeState, TsoStore.windowMap_decode]
  · simpa only [MemoryWriteWP.writeState, TsoStore.windowMap_decode] using
      writeBytes_overlay g.memory req.pa n word

/-- Every actual live successor is either the exact blocked retry, or the
single authored write with unchanged views and the own reservation cleared. -/
theorem step_inv [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (req : MemoryWriteWP.WriteRequest n) (word : BitVec (8 * n))
    (k : MemoryWriteWP.WriteResult → SailM Unit) (present : req.value = some word)
    (ram : deviceAddress req.pa = false) (plain : accessExclusive req.access_kind = false)
    (live : ThreadLive g gen) (events : List Observation) (next : Expr) (after : State)
    (forks : List Expr)
    (step : Step image (.hart gen cpu (.impure (.writeMem n req) k)) g events next after forks) :
    (¬Disjoint (Footprint req.pa n) (othersReserved g.reservations cpu) ∧
      next = .hart gen cpu (.impure (.writeMem n req) k) ∧ after = g ∧ forks = [] ∧ events = []) ∨
    (Disjoint (Footprint req.pa n) (othersReserved g.reservations cpu) ∧
      next = .hart gen cpu (k (.Ok none)) ∧ after = MemoryWriteWP.writeState g cpu req word ∧
      Effect g after cpu req word ∧ forks = [] ∧ events = []) := by
  rcases MemoryWriteWP.step_inv image g gen cpu n req word k present ram live
    events next after forks step with blocked | ⟨free, nextEq, stateEq, forkEq, eventEq⟩
  · exact Or.inl blocked
  · subst after
    exact Or.inr ⟨free, nextEq, rfl, write_effect g cpu req word plain, forkEq, eventEq⟩

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

/-- Pay the actual registered byte-window update while retaining full heap
metadata and the unchanged global-register/device portions of the bundle. -/
theorem bundle_store (era : Era.Record) (g : State) (cpu : CPU) (ξ : TsoContext.CtxId)
    (n : Nat) (req : MemoryWriteWP.WriteRequest n) (old new : BitVec (8 * n))
    (bound : n ≤ 2^64) (plain : accessExclusive req.access_kind = false) :
    iprop(⊢ MemoryWriteWP.writeBundle capacity.era era g -∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g -∗
      running capacity era cpu ξ -∗ window capacity era ξ req.pa n (.own 1) old ==∗
      MemoryWriteWP.writeBundle capacity.era era (MemoryWriteWP.writeState g cpu req new) ∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes (MemoryWriteWP.writeState g cpu req new) ∗
      running capacity era cpu ξ ∗ window capacity era ξ req.pa n (.own 1) new ∗
      ⌜TsoContextBytes.Readback (MemoryWriteWP.writeState g cpu req new) cpu req.pa n new⌝) := by
  iintro Hbundle Htso Hrun Hword
  iunfold MemoryWriteWP.writeBundle at Hbundle
  iunfold MemoryExclusiveWP.readBundle at Hbundle
  icases Hbundle with ⟨Hregs, Hheap, Hdevice⟩
  have gate := TsoContextBytesStore.ordinary (contextCapacity capacity) (contextNames era) cpu ξ
    era.imageBytes g (MemoryWriteWP.writeState g cpu req new) req.pa n old new bound
    (write_transition g cpu req new plain)
  rw [show TsoContext.heapAt (contextCapacity capacity) (contextNames era) g =
    Era.heapInterpAt capacity.era era g from rfl] at gate
  rw [show TsoContext.heapAt (contextCapacity capacity) (contextNames era)
      (MemoryWriteWP.writeState g cpu req new) =
    Era.heapInterpAt capacity.era era (MemoryWriteWP.writeState g cpu req new) from rfl] at gate
  rw [show Tso.Interp.tsoInterpAt (contextCapacity capacity).tso (contextNames era).tso era.imageBytes g =
    Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g from rfl] at gate
  rw [show Tso.Interp.tsoInterpAt (contextCapacity capacity).tso (contextNames era).tso era.imageBytes
      (MemoryWriteWP.writeState g cpu req new) =
    Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes
      (MemoryWriteWP.writeState g cpu req new) from rfl] at gate
  imod gate $$ Hheap Htso Hrun Hword with ⟨Hheap, Htso, Hrun, Hword, %reads⟩
  imodintro
  iframe Htso Hrun Hword
  isplitl [Hregs Hheap Hdevice]
  · unfold MemoryWriteWP.writeBundle MemoryExclusiveWP.readBundle
    dsimp only [MemoryWriteWP.writeState]
    iframe Hregs Hheap Hdevice
  · ipureintro
    exact reads

/-- The only write callback is constructed here. The context payer runs
inside the successful event's later; blocked events leave it unopened. -/
theorem wp_write [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    image fixed whole gen era cpu ξ (n : Nat) (req : MemoryWriteWP.WriteRequest n)
    (old new : BitVec (8 * n)) (k : MemoryWriteWP.WriteResult → SailM Unit) rr post
    (bound : n ≤ 2^64) (present : req.value = some new) (ram : deviceAddress req.pa = false)
    (plain : accessExclusive req.access_kind = false) :
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      running capacity era cpu ξ -∗ window capacity era ξ req.pa n (.own 1) old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      ▷ (∀ view, running capacity era cpu ξ -∗ window capacity era ξ req.pa n (.own 1) new -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none -∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) view -∗
        MemoryWriteWP.threadWP capacity image fixed whole (.hart gen cpu (k (.Ok none))) post) -∗
      MemoryWriteWP.threadWP capacity image fixed whole
        (.hart gen cpu (.impure (.writeMem n req) k)) post) := by
  iintro Hcert Hrun Hword Hresv Hcontinue
  iapply MemoryWriteWP.wp_write capacity (MemoryWriteWP.nativeContracts capacity)
    image fixed whole gen era cpu n req new k rr post present ram $$ Hcert Hresv
  unfold MemoryWriteWP.writePremise MemoryWriteWP.checkedPremise
  iintro %g _ Hbundle Htso
  iapply fupd_mask_intro (E2 := ∅) (by intro x h; exact CoPset.mem_full)
  iintro Hback
  iintro !>
  imod bundle_store capacity era g cpu ξ n req old new bound plain $$ Hbundle Htso Hrun Hword
    with ⟨Hbundle, Htso, Hrun, Hword, %_reads⟩
  imod Hback
  imodintro
  iframe Hbundle Htso
  iintro Hresv Hreceipt
  iapply Hcontinue $$ Hrun Hword Hresv Hreceipt

theorem actual [Platform] {hlc : HasLC} [InvGS_gen hlc GF] : Spec capacity := ⟨wp_write capacity⟩

end MachCSL.Logic.TsoContextBytesWriteWP
