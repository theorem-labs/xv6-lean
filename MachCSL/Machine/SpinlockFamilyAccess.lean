import MachCSL.Machine.SpinlockFamilyControl
import MachCSL.Machine.SpinlockAccessImage

namespace MachCSL.Machine.SpinlockFamily
open Logic Logic.SpinlockProtocol Logic.EventPlan LeanPaperStock.Functions
variable [Platform] (reads : EventWP.ReadAllowed)

omit [Platform] in
private theorem amo_word {cpu rs phase} (h : Ready cpu ⟨7, by decide⟩ rs phase) :
    SpinlockAccess.amoWord rs = 1#32 := by
  unfold SpinlockAccess.amoWord
  rw [h.operands.stage.2]
  rfl

theorem amo_plan {cpu rs phase} (h : Ready cpu ⟨7, by decide⟩ rs phase) (rr : Option Reservation) :
    Plan reads relations rs rr phase (execute (SpinlockDecode.instruction ⟨7, by decide⟩))
      (fun result after _ next => result = .Retire_Success () ∧ Completed cpu after next) := by
  obtain ⟨idle, value⟩ := h.operands.stage
  subst phase
  have word := amo_word h
  rw [SpinlockAccess.image_amo]
  refine (SpinlockAccess.amo_plan reads relations rs rr .idle h.core.toStatic h.core.off
    (h.operands.base (by decide) (by decide)) ⟨rfl, rfl⟩ ?_ ?_).mono ?_
  · intro old middle step
    cases step
    rw [word]
    exact ⟨_, _, ModeEnabled.swap old (by decide)⟩
  · intro old middle step
    cases step
    rw [word]
    exact ModeEnabled.swap old (by decide)
  · rintro _ after rr' next ⟨rfl, old, middle, rfl, rfl, readStep, writeStep⟩
    cases readStep
    rw [word] at writeStep
    cases writeStep with
    | acquire B v t visible =>
      exact ⟨rfl, SpinlockCore.write h.core _ trivial, ⟨(⟨8, by decide⟩ : Fin 17),
        ⟨fun _ _ => h.operands.participant (by decide) (by decide),
          fun _ _ => h.operands.base (by decide) (by decide),
          fun _ _ => h.operands.one (by decide) (by decide),
          by exact Or.inr ⟨B, v, t, rfl, rfl⟩⟩, ready_next h (by decide)⟩⟩
    | failed =>
      exact ⟨rfl, SpinlockCore.write h.core _ trivial, ⟨(⟨8, by decide⟩ : Fin 17),
        ⟨fun _ _ => h.operands.participant (by decide) (by decide),
          fun _ _ => h.operands.base (by decide) (by decide),
          fun _ _ => h.operands.one (by decide) (by decide), by exact Or.inl ⟨rfl, rfl⟩⟩,
        ready_next h (by decide)⟩⟩

theorem load_plan {cpu rs phase} (h : Ready cpu ⟨10, by decide⟩ rs phase) (rr : Option Reservation) :
    Plan reads relations rs rr phase (execute (SpinlockDecode.instruction ⟨10, by decide⟩))
      (fun result after _ next => result = .Retire_Success () ∧ Completed cpu after next) := by
  obtain ⟨B, v, t, rfl⟩ := h.operands.stage
  rw [SpinlockAccess.image_load]
  refine (SpinlockAccess.load_plan reads relations rs rr (.held B v t) h.core.toStatic h.core.off
    (h.operands.base (by decide) (by decide)) ⟨v, .loaded B v t, PlainStep.load B v t⟩).mono ?_
  rintro _ after rr' next ⟨word, rfl, rfl, rfl, step⟩
  cases step
  exact ⟨rfl, SpinlockCore.write h.core _ trivial, ⟨(⟨11, by decide⟩ : Fin 17),
    ⟨fun _ _ => h.operands.participant (by decide) (by decide),
      fun _ _ => h.operands.base (by decide) (by decide),
      fun _ _ => h.operands.one (by decide) (by decide), by exact ⟨B, v, t, rfl, rfl⟩⟩,
    ready_next h (by decide)⟩⟩

theorem store_plan {cpu rs phase} (h : Ready cpu ⟨12, by decide⟩ rs phase) (rr : Option Reservation) :
    Plan reads relations rs rr phase (execute (SpinlockDecode.instruction ⟨12, by decide⟩))
      (fun result after _ next => result = .Retire_Success () ∧ Completed cpu after next) := by
  obtain ⟨B, v, t, rfl, value⟩ := h.operands.stage
  have word : SpinlockAccess.storeWord rs = v + 1#32 := by
    unfold SpinlockAccess.storeWord
    rw [value]
    exact low_sign _
  rw [SpinlockAccess.image_store]
  refine (SpinlockAccess.store_plan reads relations rs rr (.loaded B v t) h.core.toStatic h.core.off
    (h.operands.base (by decide) (by decide)) ?_ ?_).mono ?_
  · rw [word]
    exact ⟨rr, .ordinary, ModeEnabled.increment B v t rr⟩
  · rw [word]
    exact ModeEnabled.increment B v t rr
  · rintro _ after rr' next ⟨rfl, rfl, rfl, step⟩
    rw [word] at step
    cases step with
    | increment _ _ _ nextTime =>
      exact ⟨rfl, h.core, ⟨(⟨13, by decide⟩ : Fin 17),
        ⟨fun _ _ => h.operands.participant (by decide) (by decide),
          fun _ _ => h.operands.base (by decide) (by decide),
          fun _ _ => h.operands.one (by decide) (by decide), by exact ⟨B, v + 1#32, nextTime, rfl⟩⟩,
        ready_next h (by decide)⟩⟩

theorem fence_plan {cpu rs phase} (h : Ready cpu ⟨13, by decide⟩ rs phase) (rr : Option Reservation) :
    Plan reads relations rs rr phase (execute (SpinlockDecode.instruction ⟨13, by decide⟩))
      (fun result after _ next => result = .Retire_Success () ∧ Completed cpu after next) := by
  obtain ⟨B, v, t, rfl⟩ := h.operands.stage
  rw [SpinlockAccess.image_fence]
  refine (SpinlockAccess.fence_plan reads relations rs rr (.stored B v t) h.core.privilege
    ⟨.stored B v t, BarrierStep.fence B v t⟩).mono ?_
  rintro _ after rr' next ⟨rfl, rfl, rfl, step⟩
  cases step
  exact ⟨rfl, h.core, ⟨(⟨14, by decide⟩ : Fin 17),
    ⟨fun _ _ => h.operands.participant (by decide) (by decide),
      fun _ _ => h.operands.base (by decide) (by decide),
      fun _ _ => h.operands.one (by decide) (by decide), by exact ⟨B, v, t, rfl⟩⟩,
    ready_next h (by decide)⟩⟩

theorem unlock_plan {cpu rs phase} (h : Ready cpu ⟨14, by decide⟩ rs phase) (rr : Option Reservation) :
    Plan reads relations rs rr phase (execute (SpinlockDecode.instruction ⟨14, by decide⟩))
      (fun result after _ next => result = .Retire_Success () ∧ Completed cpu after next) := by
  obtain ⟨B, v, t, rfl⟩ := h.operands.stage
  rw [SpinlockAccess.image_unlock]
  refine (SpinlockAccess.unlock_store_plan reads relations rs rr (.stored B v t) h.core.toStatic h.core.off
    (h.operands.base (by decide) (by decide)) ⟨rr, .ordinary, ModeEnabled.release B v t rr⟩
    (ModeEnabled.release B v t rr)).mono ?_
  rintro _ after rr' next ⟨rfl, rfl, rfl, step⟩
  cases step
  exact ⟨rfl, h.core, ⟨(⟨15, by decide⟩ : Fin 17),
    ⟨fun _ _ => h.operands.participant (by decide) (by decide),
      fun _ _ => h.operands.base (by decide) (by decide),
      fun _ _ => h.operands.one (by decide) (by decide), by rfl⟩,
    ready_next h (by decide)⟩⟩

end MachCSL.Machine.SpinlockFamily
