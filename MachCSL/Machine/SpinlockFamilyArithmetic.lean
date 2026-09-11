import MachCSL.Machine.SpinlockFamilyProofs

namespace MachCSL.Machine.SpinlockFamily
open LeanPaperStock.Functions

/-- Truncating a sign-extended architectural word retains all low 32 bits. -/
theorem low_sign (v : BitVec 32) :
    Sail.BitVec.extractLsb (sign_extend (m := 64) v) 31 0 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Sail.BitVec.extractLsb, sign_extend, Sail.BitVec.signExtend,
    BitVec.getElem_signExtend, hi, show i < 64 by omega]

theorem low_sign_add_one (v : BitVec 32) :
    Sail.BitVec.extractLsb (sign_extend (m := 64) v + 1#64) 31 0 = v + 1#32 := by
  change BitVec.extractLsb' 0 32 (sign_extend (m := 64) v + 1#64) = _
  rw [BitVec.extractLsb'_add (by decide)]
  exact congrArg (fun x : BitVec 32 => x + 1#32) (low_sign v)

theorem dispatch_word (cpu : CPU) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u (BitVec.ofNat 64 cpu.val)
      (sign_extend (m := 64) 2#12))) = if cpu.val < 2 then 1#64 else 0#64 := by
  obtain ⟨cpu, bound⟩ := cpu
  have cases : cpu = 0 ∨ cpu = 1 ∨ cpu = 2 ∨ cpu = 3 ∨ cpu = 4 ∨ cpu = 5 ∨ cpu = 6 ∨ cpu = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end MachCSL.Machine.SpinlockFamily
