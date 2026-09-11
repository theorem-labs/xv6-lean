import Xv6.Kernel.CpuOwnSpec

namespace Xv6.Kernel.CpuOwn
open MachCSL.Machine MachCSL.Logic MachCSL.Memory

theorem cpu_address (cpu : CPU) : (cpuPointer cpu).toNat = 0x800123e8 + 128 * cpu.val := by
  rcases cpu with ⟨i, bound⟩
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases cases with h | h | h | h | h | h | h | h <;> subst i <;> rfl

theorem noff_address (cpu : CPU) : (noffAddress cpu).toNat = 0x800123e8 + 128 * cpu.val + 120 := by
  change (cpuPointer cpu + 120#64).toNat = _
  rw [BitVec.toNat_add, cpu_address]
  have bound := cpu.isLt
  simp only [BitVec.toNat_ofNat]
  omega

theorem intena_address (cpu : CPU) : (intenaAddress cpu).toNat = 0x800123e8 + 128 * cpu.val + 124 := by
  change (cpuPointer cpu + 124#64).toNat = _
  rw [BitVec.toNat_add, cpu_address]
  have bound := cpu.isLt
  simp only [BitVec.toNat_ofNat]
  omega

theorem aligned cpu : TsoContextWord.Aligned (procAddress cpu) ∧
    Aligned4 (noffAddress cpu) ∧ Aligned4 (intenaAddress cpu) := by
  unfold TsoContextWord.Aligned Aligned4 procAddress
  rw [cpu_address,noff_address,intena_address]
  omega

theorem count_unsigned depth (bound : depth < 2^31) : (noffValue depth).toNat = depth := by
  simp [noffValue, Nat.mod_eq_of_lt (show depth < 2^32 by omega)]

theorem count_signed depth (bound : depth < 2^31) : (noffValue depth).toInt = (depth : Int) := by
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [count_unsigned depth bound]; omega), count_unsigned depth bound]

theorem count_injective depth depth' (bound : depth < 2^31) (bound' : depth' < 2^31)
    (same : noffValue depth = noffValue depth') : depth = depth' := by
  have := congrArg BitVec.toNat same
  simpa [count_unsigned depth bound,count_unsigned depth' bound'] using this

theorem pureSpec : PureSpec :=
  ⟨cpu_address,noff_address,intena_address,aligned,count_unsigned,count_signed,count_injective⟩

end Xv6.Kernel.CpuOwn
