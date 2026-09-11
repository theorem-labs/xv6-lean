import MachCSL.Machine.SpinlockPoolUpdateProofs

namespace MachCSL.Machine.SpinlockPool
open Logic

/-- The four body instruction boundaries are inside the event-defined holder
window. This does not constrain physical PC during an interior continuation. -/
theorem family_body_holder {cpu : CPU} {i : Fin 17} {rs : RegisterFile}
    {phase : SpinlockProtocol.Phase} (family : SpinlockFamily.Family cpu i rs phase)
    (lower : 10 ≤ i.val) (upper : i.val ≤ 13) : ∃ B, HolderPosition phase = some B := by
  have stage := family.operands.stage
  unfold SpinlockFamily.At at stage
  have cases : i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 := by omega
  rcases cases with index | index | index | index <;> rw [index] at stage
  · obtain ⟨B, v, t, rfl⟩ := stage
    exact ⟨B, rfl⟩
  · obtain ⟨B, v, t, rfl, _⟩ := stage
    exact ⟨B, rfl⟩
  · obtain ⟨B, v, t, rfl, _⟩ := stage
    exact ⟨B, rfl⟩
  · obtain ⟨B, v, t, rfl⟩ := stage
    exact ⟨B, rfl⟩

theorem boundary_holds {pool : Pool} {g : State} {cpu : CPU} {c : Cursor} {i : Fin 17}
    (inv : PoolInv (pool, g)) (on : g.power = true)
    (member : (Expr.hart g.generation cpu (.pure ()), Label.hart c) ∈ pool)
    (pc : g.registers cpu .PC = SpinlockImage.instructionAddress i)
    (lower : 10 ≤ i.val) (upper : i.val ≤ 13) : Holds (pool, g) cpu := by
  obtain ⟨_, _, _, _, _, w, _, locals, _⟩ := inv.2 on
  have control := (locals g.generation cpu (.pure ()) c member ⟨on, rfl⟩).1
  obtain ⟨j, family⟩ := EventPlanHead.pure_iff.mp control.2.2
  have agree := control.1 .PC (by simp [EventWP.IsOwned, EventWP.IsPin])
  have same := instruction_address_injective (family.pc.symm.trans (agree.symm.trans pc))
  subst j
  obtain ⟨B, holder⟩ := family_body_holder family lower upper
  exact ⟨on, .pure (), c, B, member, holder⟩

/-- A conditional corollary for two actual boundary occurrences. Full
reachability must supply PoolInv through the separately required Covers proof. -/
theorem boundary_exclusion {pool : Pool} {g : State} {cpu other : CPU}
    {c d : Cursor} {i j : Fin 17}
    (inv : PoolInv (pool, g)) (on : g.power = true)
    (left : (Expr.hart g.generation cpu (.pure ()), Label.hart c) ∈ pool)
    (right : (Expr.hart g.generation other (.pure ()), Label.hart d) ∈ pool)
    (leftPC : g.registers cpu .PC = SpinlockImage.instructionAddress i)
    (rightPC : g.registers other .PC = SpinlockImage.instructionAddress j)
    (leftBody : 10 ≤ i.val ∧ i.val ≤ 13) (rightBody : 10 ≤ j.val ∧ j.val ≤ 13) : cpu = other :=
  holder_exclusion inv
    (boundary_holds inv on left leftPC leftBody.1 leftBody.2)
    (boundary_holds inv on right rightPC rightBody.1 rightBody.2)

end MachCSL.Machine.SpinlockPool
