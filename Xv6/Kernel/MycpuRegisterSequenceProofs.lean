import Xv6.Kernel.MycpuRegisterSequenceSpec
import Xv6.Kernel.CalleeSavedProofs
import Xv6.Kernel.MycpuScalarGeometry
import MachCSL.Logic.StackPhysicalProofs

namespace Xv6.Kernel.MycpuRegisterSequence
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem push_sp (entry : RegisterFile) :
    pushed entry .x2 = StackPhysical.paStk (entry .x2) 2 := by
  change entry .x2 + (-16#64) = entry .x2 - 16#64
  simp only [BitVec.sub_eq_add_neg]

theorem framed_sp (entry : RegisterFile) : framed entry .x2 = pushed entry .x2 := by
  simp [framed, MycpuScalar.after, MachCSL.Sail.Registers.write]

theorem computed_sp (entry : RegisterFile) : computed entry .x2 = pushed entry .x2 := by
  simp [computed, MycpuScalar.addressCalc, MycpuScalar.offsetCalc,
    MycpuScalar.after, MachCSL.Sail.Registers.write, framed_sp]

theorem popped_sp (entry : RegisterFile) : popped entry .x2 = entry .x2 := by
  simp only [popped, MycpuScalar.after]
  simp only [MachCSL.Sail.Registers.write_same]
  have restored_sp : restored entry .x2 = computed entry .x2 := by
    simp [restored, MycpuMemory.after, MachCSL.Sail.Registers.write]
  rw [restored_sp, computed_sp, push_sp]
  change (entry .x2 - 16#64) + 16#64 = entry .x2
  exact BitVec.sub_add_cancel _ _

theorem computed_result (entry : RegisterFile) :
    computed entry .x10 = MycpuScalar.mycpuRet (entry .x4) := by
  unfold computed
  rw [MycpuScalar.result _ (by simp)]
  simp [framed, pushed, MycpuScalar.after, MachCSL.Sail.Registers.write]

theorem saved_ra (entry : RegisterFile) : returned entry .x1 = entry .x1 := by
  simp [returned, MycpuReturn.after, popped, restored, MycpuScalar.after,
    MycpuMemory.after, MachCSL.Sail.Registers.write]

theorem saved_s0 (entry : RegisterFile) : returned entry .x8 = entry .x8 := by
  simp [returned, MycpuReturn.after, popped, restored, MycpuScalar.after,
    MycpuMemory.after, MachCSL.Sail.Registers.write]

theorem saved_sp (entry : RegisterFile) : returned entry .x2 = entry .x2 := by
  simpa [returned, MycpuReturn.after, MachCSL.Sail.Registers.write] using popped_sp entry

theorem result (entry : RegisterFile) :
    returned entry .x10 = MycpuScalar.mycpuRet (entry .x4) := by
  simpa [returned, MycpuReturn.after, popped, restored, MycpuScalar.after,
    MycpuMemory.after, MachCSL.Sail.Registers.write] using computed_result entry

theorem return_address (entry : RegisterFile) :
    returned entry .nextPC = MycpuReturn.retPC (entry .x1) := by
  simp [returned, MycpuReturn.after, popped, restored, MycpuScalar.after,
    MycpuMemory.after, MachCSL.Sail.Registers.write]

theorem abi (entry : RegisterFile) : CalleeSaved.Preserved entry (returned entry) := by
  rw [CalleeSaved.preserved_iff]
  refine ⟨saved_sp entry, saved_s0 entry, ?_⟩
  simp [returned, MycpuReturn.after, popped, restored, computed, framed, pushed,
    MycpuScalar.addressCalc, MycpuScalar.offsetCalc, MycpuScalar.after,
    MycpuMemory.after, MachCSL.Sail.Registers.write]

theorem actual : Spec := ⟨abi, result, return_address, saved_ra⟩

end Xv6.Kernel.MycpuRegisterSequence
