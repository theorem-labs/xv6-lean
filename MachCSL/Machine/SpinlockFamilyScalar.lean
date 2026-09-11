import MachCSL.Machine.SpinlockFamilyArithmetic
import MachCSL.Machine.SpinlockScalarProofs
import MachCSL.Machine.SpinlockControlProofs

namespace MachCSL.Machine.SpinlockFamily
open Logic.SpinlockProtocol LeanPaperStock.Functions
set_option maxRecDepth 10000

private theorem sequential (rs : RegisterFile) (i : Fin 17)
    (next : rs .nextPC = Sail.BitVec.addInt (rs .PC) 4)
    (pc : rs .PC = SpinlockImage.instructionAddress i) (bound : i.val < 16) :
    rs .nextPC = SpinlockImage.instructionAddress ⟨i.val + 1, by omega⟩ := by
  rw [next, pc]
  obtain ⟨i, hi⟩ := i
  dsimp only at bound
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem ready_next {cpu i rs phase} (h : Ready cpu i rs phase) (bound : i.val < 16) :
    rs .nextPC = SpinlockImage.instructionAddress ⟨i.val + 1, by omega⟩ :=
  sequential rs i h.nextPC h.pc bound

theorem csr_completed {cpu rs phase} (h : Ready cpu ⟨0, by decide⟩ rs phase) :
    Completed cpu (SpinlockControl.csrAfter rs) phase := by
  refine ⟨SpinlockCore.csr h.core, ⟨⟨1, by decide⟩, ?_, ready_next h (by exact of_decide_eq_true rfl)⟩⟩
  refine ⟨by simp, by simp, by simp, ?_⟩
  exact ⟨h.operands.stage, h.core.hartid⟩

theorem scalar_completed {cpu rs phase} (j : Fin 7)
    (h : Ready cpu (SpinlockScalar.index j) rs phase) :
    Completed cpu (SpinlockScalar.after j rs) phase := by
  obtain ⟨j, hj⟩ := j
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have stage := h.operands.stage
    have part := h.operands.participant
    have base := h.operands.base
    have one := h.operands.one
    have next := ready_next h (by exact of_decide_eq_true rfl)
    have pc := h.pc
    refine ⟨SpinlockCore.scalar h.core _, ⟨⟨_, by exact of_decide_eq_true rfl⟩, ?_, next⟩⟩
    refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [SpinlockScalar.index, At, SpinlockScalar.after, Sail.Registers.write,
      ↓reduceDIte] at stage part base one pc next ⊢
  all_goals try (intro lo hi; omega)
  all_goals try assumption
  all_goals simp_all [dispatch_word]
  all_goals try rfl
  · rcases stage with ⟨idle, hv⟩ | ⟨held, hv⟩
    · exact Or.inl ⟨idle, by rw [hv]; rfl⟩
    · exact Or.inr ⟨held, by rw [hv]; rfl⟩
  · obtain ⟨B, v, loaded, hv⟩ := stage
    refine ⟨B, v, loaded, ?_⟩
    rw [hv]
    exact congrArg (sign_extend (m := 64)) (low_sign_add_one v)

end MachCSL.Machine.SpinlockFamily
