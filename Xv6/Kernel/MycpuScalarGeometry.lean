import Xv6.Kernel.MycpuScalarDefs

namespace Xv6.Kernel.MycpuScalar
open MachCSL.Machine LeanPaperStock.Functions

theorem offset_result (rs : RegisterFile) : offsetCalc rs .x15 = mycpuA5 (rs .x4) := by
  simp [offsetCalc, after, MachCSL.Sail.Registers.write, mycpuA5]

theorem offset_pc (rs : RegisterFile) : offsetCalc rs .PC = rs .PC := by
  simp [offsetCalc, after, MachCSL.Sail.Registers.write]

/-- These six scalar state updates form the source return expression when AUIPC
reads its actual instruction PC. This is not a fetched-cycle composition theorem. -/
theorem result (rs : RegisterFile) (pc : rs .PC = MycpuDecode.address ⟨7, by decide⟩) :
    addressCalc (offsetCalc rs) .x10 = mycpuRet (rs .x4) := by
  simp [addressCalc, after, MachCSL.Sail.Registers.write, offset_pc, offset_result, pc, mycpuRet] <;> rfl

theorem linked_cpus (tp : BitVec 64) :
    mycpuRet tp = BitVec.ofInt 64 MycpuDecode.cpusAddress + mycpuA5 tp := by
  rfl

/-- The actual hart-index specialization, with the full modular statement above
available for arbitrary TP values. No hart identity is assumed by scalar WPs. -/
theorem valid_hart (cpu : CPU) :
    (mycpuRet (BitVec.ofNat 64 cpu.val)).toNat = 0x800123e8 + 128 * cpu.val := by
  obtain ⟨cpu, bound⟩ := cpu
  have cases : cpu = 0 ∨ cpu = 1 ∨ cpu = 2 ∨ cpu = 3 ∨ cpu = 4 ∨ cpu = 5 ∨ cpu = 6 ∨ cpu = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

end Xv6.Kernel.MycpuScalar
