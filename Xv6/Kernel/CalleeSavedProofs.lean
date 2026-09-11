import Xv6.Kernel.CalleeSavedSpec

namespace Xv6.Kernel.CalleeSaved
open MachCSL.Machine

theorem preserved_iff (a b : RegisterFile) : Preserved a b ↔
    b .x2 = a .x2 ∧ b .x8 = a .x8 ∧ b .x9 = a .x9 ∧
    b .x18 = a .x18 ∧ b .x19 = a .x19 ∧ b .x20 = a .x20 ∧
    b .x21 = a .x21 ∧ b .x22 = a .x22 ∧ b .x23 = a .x23 ∧
    b .x24 = a .x24 ∧ b .x25 = a .x25 ∧ b .x26 = a .x26 ∧
    b .x27 = a .x27 := by
  simp [Preserved, registers]

theorem preserved_refl (rs : RegisterFile) : Preserved rs rs := fun _ _ => rfl

theorem preserved_trans (a b c : RegisterFile) (ab : Preserved a b)
    (bc : Preserved b c) : Preserved a c :=
  fun r member => (bc r member).trans (ab r member)

theorem caller_write (a b : RegisterFile) (r : Register) (value : RegisterType r)
    (caller : r ∉ registers) (same : Preserved a b) :
    Preserved a (MachCSL.Sail.Registers.write b r value) := by
  intro c member
  have ne : r ≠ c := fun eq => caller (eq ▸ member)
  rw [MachCSL.Sail.Registers.write_other _ _ _ _ ne]
  exact same c member

theorem outerWrite_cons_eq (r : Register) (value : RegisterType r) (rest : List Write) :
    outerWrite r (⟨r, value⟩ :: rest) = some value := by simp [outerWrite]

theorem outerWrite_cons_ne (r k : Register) (value : RegisterType k) (rest : List Write)
    (ne : k ≠ r) : outerWrite r (⟨k, value⟩ :: rest) = outerWrite r rest := by
  simp [outerWrite, ne]

theorem applyWrites_lookup (writes : List Write) (rs : RegisterFile) (r : Register) :
    applyWrites writes rs r = (outerWrite r writes).getD (rs r) := by
  induction writes with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨k, value⟩
    by_cases eq : k = r
    · subst k
      simp [applyWrites, outerWrite, MachCSL.Sail.Registers.write]
    · simpa [applyWrites, outerWrite, MachCSL.Sail.Registers.write, eq] using ih

theorem applyWrites_preserved_iff (rs : RegisterFile) (writes : List Write) :
    Preserved rs (applyWrites writes rs) ↔ Restores rs writes := by
  constructor
  · intro same r member value found
    have h := same r member
    simpa [applyWrites_lookup, found] using h
  · intro restored r member
    rw [applyWrites_lookup]
    cases found : outerWrite r writes with
    | none => rfl
    | some value => exact restored r member value found

theorem applyWrites_preserved (rs : RegisterFile) (writes : List Write)
    (restored : Restores rs writes) : Preserved rs (applyWrites writes rs) :=
  (applyWrites_preserved_iff rs writes).mpr restored

theorem tp_not_saved : Register.x4 ∉ registers := by decide

theorem actual : Spec :=
  ⟨preserved_refl, preserved_trans, caller_write, applyWrites_preserved⟩

end Xv6.Kernel.CalleeSaved
