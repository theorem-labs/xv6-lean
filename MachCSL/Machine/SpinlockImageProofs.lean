import MachCSL.Machine.SpinlockImageDefs

namespace MachCSL.Machine.SpinlockImage
open MachCSL.Memory
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem code_length : code.length = 68 := rfl

theorem instruction_bytes (i : Fin 17) :
    readBytes (loadedRam image) (instructionAddress i) 4 = some (word i) := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cbv

theorem lock_initial : readBytes (loadedRam image) lockAddress 4 = some 0#32 := rfl
theorem counter_initial : readBytes (loadedRam image) counterAddress 4 = some 0#32 := rfl

theorem data_separate : Disjoint (Footprint lockAddress 4) (Footprint counterAddress 4) := by
  intro a ⟨i, hi, ei⟩ ⟨j, hj, ej⟩
  have eq := congrArg BitVec.toNat (ei.trans ej.symm)
  simp [addressAdd, lockAddress, counterAddress, BitVec.toNat_add, Nat.mod_eq_of_lt] at eq
  omega

theorem instruction_address (i : Fin 17) :
    (instructionAddress i).toNat = 0x80000000 + 4 * i.val := by
  have bound := i.isLt
  simp only [instructionAddress, base, BitVec.toNat_ofInt]
  omega

theorem instruction_ram (i : Fin 17) :
    ramLow ≤ (instructionAddress i).toNat ∧ (instructionAddress i).toNat + 4 ≤ ramHigh := by
  rw [instruction_address]
  have := i.isLt
  unfold ramLow ramHigh
  omega

theorem code_lock_separate (i : Fin 17) :
    Disjoint (Footprint (instructionAddress i) 4) (Footprint lockAddress 4) := by
  intro a ⟨j, hj, ej⟩ ⟨k, hk, ek⟩
  have equal := congrArg BitVec.toNat (ej.trans ek.symm)
  simp only [addressAdd, BitVec.toNat_add, BitVec.toNat_ofNat, instruction_address,
    lockAddress, BitVec.toNat_ofNat] at equal
  have := i.isLt
  omega

theorem code_counter_separate (i : Fin 17) :
    Disjoint (Footprint (instructionAddress i) 4) (Footprint counterAddress 4) := by
  intro a ⟨j, hj, ej⟩ ⟨k, hk, ek⟩
  have equal := congrArg BitVec.toNat (ej.trans ek.symm)
  simp only [addressAdd, BitVec.toNat_add, BitVec.toNat_ofNat, instruction_address,
    counterAddress, BitVec.toNat_ofNat] at equal
  have := i.isLt
  omega

end MachCSL.Machine.SpinlockImage
