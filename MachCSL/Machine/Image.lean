import MachCSL.Machine.Platform
import MachCSL.Memory.Bytes

namespace MachCSL.Machine
open Memory

structure BootImage where
  vector : BitVec 64
  byte : Int → Byte

def loadedRam (image : BootImage) : ByteMap 64 := fun a =>
  if ramLow ≤ a.toNat ∧ a.toNat < ramHigh then some (image.byte a.toNat) else none

/-- The two RAM clauses of the source boot predicate, before normalization. -/
def RamShape (image : BootImage) (memory : ByteMap 64) : Prop :=
  (∀ a b, memory a = some b → ramLow ≤ a.toNat ∧ a.toNat < ramHigh) ∧
  (∀ a : Int, (ramLow : Int) ≤ a → a < (ramHigh : Int) →
    memory (BitVec.ofInt 64 a) = some (image.byte a))

private theorem ram_address_roundtrip (a : Int) (low : (ramLow : Int) ≤ a)
    (high : a < (ramHigh : Int)) : ((BitVec.ofInt 64 a).toNat : Int) = a := by
  have ha : 0 ≤ a := by unfold ramLow at low; omega
  have hb : a < 18446744073709551616 := by unfold ramHigh at high; omega
  simp only [BitVec.toNat_ofInt]
  change ((a % 18446744073709551616).toNat : Int) = a
  rw [Int.emod_eq_of_lt ha hb, Int.toNat_of_nonneg ha]

theorem loadedRam_shape (image : BootImage) : RamShape image (loadedRam image) := by
  constructor
  · intro a b h
    unfold loadedRam at h
    split at h
    · assumption
    · contradiction
  · intro a low high
    have h := ram_address_roundtrip a low high
    have bounds : ramLow ≤ (BitVec.ofInt 64 a).toNat ∧ (BitVec.ofInt 64 a).toNat < ramHigh := by
      omega
    simp only [loadedRam, if_pos bounds, h]

/-- Equality to loadedRam preserves exactly the source domain and byte clauses. -/
theorem ramShape_iff (image : BootImage) (memory : ByteMap 64) :
    RamShape image memory ↔ memory = loadedRam image := by
  constructor
  · rintro ⟨domain, contents⟩
    funext a
    by_cases bounds : ramLow ≤ a.toNat ∧ a.toNat < ramHigh
    · have h := contents (a.toNat : Int) (by omega) (by omega)
      simpa [loadedRam, bounds] using h
    · have h : memory a = none := by
        cases hm : memory a with
        | none => rfl
        | some b => exact False.elim (bounds (domain a b hm))
      simp [loadedRam, bounds, h]
  · rintro rfl
    exact loadedRam_shape image

end MachCSL.Machine
