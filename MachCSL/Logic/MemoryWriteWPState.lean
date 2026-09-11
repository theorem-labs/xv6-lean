import MachCSL.Logic.MemoryWriteWPSpec
import MachCSL.Logic.RegisterWPProofs
import MachCSL.Machine.NodeInvariants

namespace MachCSL.Logic.MemoryWriteWP
open Iris Iris.Std Iris.BI Iris.ProgramLogic MachCSL.Memory MachCSL.Machine

@[simp] theorem writeState_view (g : State) (cpu : CPU) (req : WriteRequest n) (value : BitVec (8 * n)) :
    (writeState g cpu req value).views cpu = postView g cpu req := by simp [writeState, updateHart]

theorem writeBack_write (g : State) (cpu : CPU) (req : WriteRequest n) (value : BitVec (8 * n)) :
    writeBack g cpu { focus g cpu with
      memory := writeBytes g.memory req.pa n value
      log := g.log ++ [⟨snapshot req.pa n value, hartAgent cpu⟩]
      view := postView g cpu req
      reservation := none } = writeState g cpu req value := by
  have same {α : Type} (f : CPU → α) : updateHart f cpu (f cpu) = f := by
    funext other
    by_cases h : other = cpu <;> simp [updateHart, h]
  simp only [writeBack, focus, writeState, same]

theorem blocked_step [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (n : Nat) (req : WriteRequest n) (value : BitVec (8 * n)) (k : WriteResult → SailM Unit)
    (present : req.value = some value) (ram : deviceAddress req.pa = false)
    (live : ThreadLive g gen) (blocked : ¬Disjoint (Footprint req.pa n) (othersReserved g.reservations cpu)) :
    Step image (.hart gen cpu (.impure (.writeMem n req) k)) g []
      (.hart gen cpu (.impure (.writeMem n req) k)) g [] := by
  apply Step.hartLive _ _ _ _ _ _ live
  refine ⟨focus g cpu, ?_, (RegisterWP.writeBack_focus g cpu).symm⟩
  simp only [NodeStep, present, ram, Bool.false_eq_true, ↓reduceIte]
  exact Or.inl ⟨blocked, True.intro, True.intro⟩

theorem written_step [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (n : Nat) (req : WriteRequest n) (value : BitVec (8 * n)) (k : WriteResult → SailM Unit)
    (present : req.value = some value) (ram : deviceAddress req.pa = false)
    (live : ThreadLive g gen) (free : Disjoint (Footprint req.pa n) (othersReserved g.reservations cpu)) :
    Step image (.hart gen cpu (.impure (.writeMem n req) k)) g []
      (.hart gen cpu (k (.Ok none))) (writeState g cpu req value) [] := by
  apply Step.hartLive _ _ _ _ _ _ live
  refine ⟨{ focus g cpu with
    memory := writeBytes g.memory req.pa n value
    log := g.log ++ [⟨snapshot req.pa n value, hartAgent cpu⟩]
    view := postView g cpu req
    reservation := none }, ?_, (writeBack_write g cpu req value).symm⟩
  simp only [NodeStep, present, ram, Bool.false_eq_true, ↓reduceIte]
  exact Or.inr ⟨free, True.intro, rfl⟩

theorem step_inv [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (n : Nat) (req : WriteRequest n) (value : BitVec (8 * n)) (k : WriteResult → SailM Unit)
    (present : req.value = some value) (ram : deviceAddress req.pa = false)
    (live : ThreadLive g gen) (events : List Observation) (e' : Expr) (g' : State) (forks : List Expr)
    (step : Step image (.hart gen cpu (.impure (.writeMem n req) k)) g events e' g' forks) :
    (¬Disjoint (Footprint req.pa n) (othersReserved g.reservations cpu) ∧
      e' = .hart gen cpu (.impure (.writeMem n req) k) ∧ g' = g ∧ forks = [] ∧ events = []) ∨
    (Disjoint (Footprint req.pa n) (othersReserved g.reservations cpu) ∧
      e' = .hart gen cpu (k (.Ok none)) ∧ g' = writeState g cpu req value ∧ forks = [] ∧ events = []) := by
  cases step with
  | hartDead _ _ _ _ dead => exact False.elim (dead live)
  | hartLive _ _ _ m' _ _ _ h =>
    obtain ⟨after, node, hg⟩ := h
    simp only [NodeStep, present, ram, Bool.false_eq_true, ↓reduceIte] at node
    rcases node with ⟨blocked, hm, hs⟩ | ⟨free, hm, hs⟩
    · subst after; subst m'
      exact Or.inl ⟨blocked, rfl, hg.trans (RegisterWP.writeBack_focus g cpu), rfl, rfl⟩
    · subst after; subst m'
      exact Or.inr ⟨free, rfl, hg.trans (writeBack_write g cpu req value), rfl, rfl⟩

/-- The runtime builtin handles absent payloads purely. An explicitly forged
absent-payload event has no live machine successor, rather than a fake write. -/
theorem absent_event_no_step [Platform] (image : BootImage) (g : State) (gen : Nat) (cpu : CPU)
    (n : Nat) (req : WriteRequest n) (k : WriteResult → SailM Unit) (absent : req.value = none)
    (live : ThreadLive g gen) (events : List Observation) (e' : Expr) (g' : State) (forks : List Expr) :
    ¬Step image (.hart gen cpu (.impure (.writeMem n req) k)) g events e' g' forks := by
  intro step
  cases step with
  | hartDead _ _ _ _ dead => exact dead live
  | hartLive _ _ _ _ _ _ _ h =>
    obtain ⟨after, node, _⟩ := h
    simp only [NodeStep, absent] at node

theorem writeState_reservationsOK (g : State) (cpu : CPU) (req : WriteRequest n)
    (value : BitVec (8 * n)) (ok : ReservationsOK g)
    (free : Disjoint (Footprint req.pa n) (othersReserved g.reservations cpu)) :
    ReservationsOK (writeState g cpu req value) := by
  intro other reserved found
  change updateHart g.reservations cpu none other = some reserved at found
  by_cases same : other = cpu
  · simp [updateHart, same] at found
  · simp only [updateHart, if_neg same] at found
    apply writeBytes_preserves_submap g.memory reserved req.pa n value (ok other reserved found)
    intro a footprint domain
    exact free a footprint ⟨other, same, reserved, found, domain⟩

theorem writeState_transition (g : State) (cpu : CPU) (req : WriteRequest n)
    (value : BitVec (8 * n)) (ok : MemoryOK g) :
    TsoStore.WindowTransition g (writeState g cpu req value) req.pa n value (hartAgent cpu) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro other
    by_cases same : other = cpu
    · subst other
      rw [writeState_view]
      unfold postView
      split
      · exact Nat.le_trans (ok.2.1 cpu) (Nat.le_succ _)
      · exact Nat.le_refl _
    · simp [writeState, updateHart, same]
  · intro other
    have old := ok.2.1 other
    simp only [writeState, updateHart, List.length_append, List.length_singleton]
    split
    · subst other
      unfold postView
      split <;> omega
    · omega

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

theorem tso_receipt (views : Tso.Views.ViewsSpec capacity.era.views)
    (era : Era.Record) (g : State) (cpu : CPU) :
    iprop(⊢ Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g -∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g ∗
      Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) (g.views cpu)) := by
  unfold Tso.Interp.tsoInterpAt Era.Capacity.tso Era.Record.tsoNames
  iintro ⟨%timestamps, %entries, Hts, %domain, %tie, Hlog, %rep, Hlen, Hv, %ok⟩
  ihave ⟨Hv, Hlen, Hreceipt⟩ := views.get era.views era.logLength (Tso.Interp.avf g)
    (hartAgent cpu) g.log.length (Tso.Interp.avf_bound g ok.1 _) $$ Hv Hlen
  rw [Tso.Interp.avf_hart]
  iframe
  ipureintro
  exact ⟨domain, tie, rep, ok⟩

/-- Only the fixed generation, power and durable-disk fields are framed. -/
theorem power_write_access (fixed : MachineInterp.FixedNames) (g : State) (gen : Nat)
    (era : Era.Record) (cpu : CPU) (req : WriteRequest n) (value : BitVec (8 * n)) (live : ThreadLive g gen) :
    iprop(⊢ MachineInterp.powerInterp capacity fixed g -∗
      MachineInterp.generationCertificate capacity fixed gen era -∗
      Era.interp capacity.era era g ∗
      (Era.interp capacity.era era (writeState g cpu req value) -∗
        MachineInterp.powerInterp capacity fixed (writeState g cpu req value))) := by
  unfold MachineInterp.powerInterp MachineInterp.generationCertificate PowerGhost.counterInterp
  rw [live.1, live.2]
  simp only [↓reduceIte]
  iintro ⟨Hc, Hd, %entries, Hr, %domain, %current, %lookup, Hera⟩ ⟨_, _, Hregistered⟩
  ihave %registered := Era.registry_lookup capacity.registry fixed.registry entries gen era $$ Hr Hregistered
  have same : current = era := Option.some.inj (lookup.symm.trans registered)
  subst current
  isplitl [Hera]
  · iexact Hera
  · iintro Hera
    isimp only [PowerGhost.startCount, live.1, live.2, ↓reduceIte] at Hc
    simp only [PowerGhost.startCount, live.1, live.2, ↓reduceIte] at domain
    simp only [writeState, PowerGhost.startCount, live.1, live.2, ↓reduceIte]
    iframe
    ipureintro
    exact ⟨domain, lookup⟩

theorem bundle_write_access (views : Tso.Views.ViewsSpec capacity.era.views)
    (reservations : Reservations.ReservationSpec capacity.era.reservations)
    (era : Era.Record) (g : State) (cpu : CPU) (req : WriteRequest n) (value : BitVec (8 * n))
    (free : Disjoint (Footprint req.pa n) (othersReserved g.reservations cpu)) :
    iprop(⊢ Era.interp capacity.era era g -∗ writeBundle capacity.era era g ∗
      Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes g ∗
      (∀ rr, writeBundle capacity.era era (writeState g cpu req value) -∗
        Tso.Interp.tsoInterpAt capacity.era.tso era.tsoNames era.imageBytes (writeState g cpu req value) -∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu rr ==∗
        Era.interp capacity.era era (writeState g cpu req value) ∗
        Reservations.resvFrag capacity.era.reservations era.reservations cpu none ∗
        Tso.Views.viewLB capacity.era.views era.views era.logLength (hartAgent cpu) (postView g cpu req))) := by
  unfold Era.interp writeBundle MemoryExclusiveWP.readBundle
  iintro ⟨Hr, Hheap, Hd, Hdisk, Htso, Hresv, %ok⟩
  iframe Hr Hheap Hd Htso
  iintro %rr ⟨Hr, Hheap, Hd⟩ Htso Hfrag
  imod reservations.update era.reservations g.reservations cpu rr none $$ Hresv Hfrag with ⟨Hresv, Hfrag⟩
  ihave ⟨Htso, Hreceipt⟩ := tso_receipt capacity views era (writeState g cpu req value) cpu $$ Htso
  rw [writeState_view]
  imodintro
  iframe Hfrag Hreceipt
  dsimp only [writeState]
  iframe
  ipureintro
  exact writeState_reservationsOK g cpu req value ok free

end MachCSL.Logic.MemoryWriteWP
