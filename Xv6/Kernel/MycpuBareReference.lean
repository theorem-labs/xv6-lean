import Xv6.Kernel.MycpuBareState

namespace Xv6.Kernel.MycpuBare
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

@[simp] theorem reference_zero (entry : RegisterFile) (r : Register) : reference entry 0 r = entry r := rfl

@[simp] theorem reference_x1 (entry : RegisterFile) (k : Nat) :
    reference entry (k+1) .x1 = (if k = 10 then entry .x1 else reference entry k .x1) := by
  simpa [reference, SupervisorRetirement.tickPCAfter, MachCSL.Sail.Registers.write] using
    (body_values entry k (reference entry k)).1

@[simp] theorem reference_x2 (entry : RegisterFile) (k : Nat) :
    reference entry (k+1) .x2 = (if k = 0 then reference entry k .x2 + (-16#64) else if k = 12 then reference entry k .x2 + 16#64 else reference entry k .x2) := by
  simpa [reference, SupervisorRetirement.tickPCAfter, MachCSL.Sail.Registers.write] using
    (body_values entry k (reference entry k)).2.1

@[simp] theorem reference_x4 (entry : RegisterFile) (k : Nat) :
    reference entry (k+1) .x4 = reference entry k .x4 := by
  simpa [reference, SupervisorRetirement.tickPCAfter, MachCSL.Sail.Registers.write] using
    (body_values entry k (reference entry k)).2.2.1

@[simp] theorem reference_x8 (entry : RegisterFile) (k : Nat) :
    reference entry (k+1) .x8 = (if k = 3 then reference entry k .x2 + 16#64 else if k = 11 then entry .x8 else reference entry k .x8) := by
  simpa [reference, SupervisorRetirement.tickPCAfter, MachCSL.Sail.Registers.write] using
    (body_values entry k (reference entry k)).2.2.2.1

@[simp] theorem reference_x10 (entry : RegisterFile) (k : Nat) :
    reference entry (k+1) .x10 = (if k = 7 then reference entry k .PC + 0x11000#64 else if k = 8 then reference entry k .x10 + sign_extend (m := 64) 0xb20#12 else if k = 9 then reference entry k .x10 + reference entry k .x15 else reference entry k .x10) := by
  simpa [reference, SupervisorRetirement.tickPCAfter, MachCSL.Sail.Registers.write] using
    (body_values entry k (reference entry k)).2.2.2.2.1

@[simp] theorem reference_x15 (entry : RegisterFile) (k : Nat) :
    reference entry (k+1) .x15 = (if k = 4 then reference entry k .x4 else if k = 5 then sign_extend (m := 64) (_root_.Sail.BitVec.extractLsb (reference entry k .x15) 31 0) else if k = 6 then _root_.Sail.shift_bits_left (reference entry k .x15) 7#6 else reference entry k .x15) := by
  simpa [reference, SupervisorRetirement.tickPCAfter, MachCSL.Sail.Registers.write] using
    (body_values entry k (reference entry k)).2.2.2.2.2.1

@[simp] theorem reference_PC (entry : RegisterFile) (k : Nat) :
    reference entry (k+1) .PC = (if k < 13 then reference entry k .PC + BitVec.ofNat 64 (stepWidth k) else MycpuReturn.retPC (reference entry k .x1)) := by
  simpa [reference, SupervisorRetirement.tickPCAfter, MachCSL.Sail.Registers.write] using
    (body_values entry k (reference entry k)).2.2.2.2.2.2

@[simp] theorem reference_nextPC (entry : RegisterFile) (k : Nat) :
    reference entry (k+1) .nextPC = (if k < 13 then reference entry k .PC + BitVec.ofNat 64 (stepWidth k) else MycpuReturn.retPC (reference entry k .x1)) := by
  simpa [reference, SupervisorRetirement.tickPCAfter, MachCSL.Sail.Registers.write] using
    (body_values entry k (reference entry k)).2.2.2.2.2.2

set_option linter.unusedSimpArgs false in
theorem reference_pc (entry : RegisterFile) (entryPC : entry .PC = MycpuDecode.address ⟨0, by decide⟩)
    (k : Nat) (bound : k ≤ 14) : reference entry k .PC = pcAt entry k := by
  have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [pcAt, stepWidth, entryPC, MycpuDecode.address, MycpuDecode.offset, MycpuDecode.base]
  all_goals rfl

theorem reference_next_pc (entry : RegisterFile) (k : Nat) (positive : 0 < k) :
    reference entry k .nextPC = reference entry k .PC := by
  cases k with
  | zero => omega
  | succ k => simp

theorem reference_ra (entry : RegisterFile) (k : Nat) : reference entry k .x1 = entry .x1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ih]

theorem reference_tp (entry : RegisterFile) (k : Nat) : reference entry k .x4 = entry .x4 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa using ih

theorem phase_register {entry rs : RegisterFile} {k : Nat} (phase : Phase entry k rs)
    (r : Register) (outside : r ∉ ignored) : rs r = reference entry k r := phase.core r outside

theorem phase_address {entry rs : RegisterFile} {k : Nat} (entryPC : entry .PC = MycpuDecode.address ⟨0, by decide⟩)
    (phase : Phase entry k rs) (bound : k < 14) : rs .PC = MycpuDecode.address ⟨k, bound⟩ := by
  rw [phase.pc, reference_pc entry entryPC k (by omega)]
  simp [pcAt, bound]

theorem reference_sp (entry : RegisterFile) (k : Nat) (positive : 0 < k) (bound : k ≤ 12) :
    reference entry k .x2 = StackPhysical.paStk (entry .x2) 2 := by
  have cases : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [StackPhysical.paStk, BitVec.sub_eq_add_neg]

theorem phase_stack_address {entry rs : RegisterFile} {k : Nat} (phase : Phase entry k rs)
    (positive : 0 < k) (bound : k ≤ 12) (slot : MycpuMemory.Slot) :
    MycpuMemory.address slot rs = (match slot with | .ra => raSlot entry | .s0 => s0Slot entry) := by
  have sp : rs .x2 = StackPhysical.paStk (entry .x2) 2 :=
    (phase_register phase .x2 (by decide)).trans (reference_sp entry k positive bound)
  cases slot with
  | ra => simpa [MycpuMemory.address, MycpuMemory.offset, sp, raSlot, MachCSL.Memory.addressAdd] using
      (StackPhysical.frame_two_addresses (entry .x2)).1
  | s0 => simp [MycpuMemory.address, MycpuMemory.offset, sp, s0Slot]

theorem phase_store_ra {entry rs : RegisterFile} (phase : Phase entry 1 rs) :
    MycpuMemory.dataValue .ra rs = entry .x1 := by
  exact (phase_register phase .x1 (by decide)).trans (reference_ra entry 1)

theorem phase_store_s0 {entry rs : RegisterFile} (phase : Phase entry 2 rs) :
    MycpuMemory.dataValue .s0 rs = entry .x8 := by
  simpa [MycpuMemory.dataValue] using phase_register phase .x8 (by decide)

theorem reference_final_sp (entry : RegisterFile) : reference entry 14 .x2 = entry .x2 := by
  calc
    reference entry 14 .x2 = reference entry 13 .x2 := reference_x2 entry 13
    _ = reference entry 12 .x2 + 16#64 := reference_x2 entry 12
    _ = StackPhysical.paStk (entry .x2) 2 + 16#64 := congrArg (· + 16#64) (reference_sp entry 12 (by decide) (by decide))
    _ = entry .x2 := BitVec.sub_add_cancel _ _

theorem reference_final_s0 (entry : RegisterFile) : reference entry 14 .x8 = entry .x8 := by simp

theorem reference_final_result (entry : RegisterFile) (entryPC : entry .PC = MycpuDecode.address ⟨0, by decide⟩) :
    reference entry 14 .x10 = MycpuScalar.mycpuRet (entry .x4) := by
  simp [stepWidth, entryPC, MycpuDecode.address, MycpuDecode.offset, MycpuDecode.base,
    MycpuScalar.mycpuRet, MycpuScalar.mycpuA5]
  rw [show sign_extend (m := 64) 0#12 = 0#64 from rfl, BitVec.add_zero]

theorem phase_final_saved {entry rs : RegisterFile} (phase : Phase entry 14 rs) :
    CalleeSaved.Preserved entry rs := by
  intro r member
  have core := phase_register phase r (by
    have apart : List.Disjoint CalleeSaved.registers ignored := by simp [List.Disjoint, CalleeSaved.registers, ignored]
    exact apart member)
  rw [core]
  simp only [CalleeSaved.registers, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reference_final_sp entry
  · exact reference_final_s0 entry
  all_goals exact reference_other entry 14 _ (by decide) (by decide)

theorem phase_result {entry rs : RegisterFile} (config : EntryConfig entry) (phase : Phase entry 14 rs) :
    Result entry rs := by
  have stable := phase_stable entry 14 rs phase
  have pc : rs .PC = MycpuReturn.retPC (entry .x1) := by
    rw [phase.pc, reference_pc entry config.pc 14 (by decide)]
    rfl
  refine ⟨stable_config config.toSupervisorConfig stable, stable, pc, ?_, phase_final_saved phase, ?_, ?_⟩
  · rw [phase.nextPC (by decide), reference_next_pc entry 14 (by decide)]
    exact phase.pc.symm.trans pc
  · exact (phase_register phase .x1 (by decide)).trans (reference_ra entry 14)
  · exact (phase_register phase .x10 (by decide)).trans (reference_final_result entry config.pc)

/-- Independent arithmetic bookkeeping agrees with the source-shaped register
sequence outside the actual clock/retirement control fields. This is a pure
projection equality, not an execution witness. -/
theorem reference_returned (entry : RegisterFile)
    (entryPC : entry .PC = MycpuDecode.address ⟨0, by decide⟩) :
    CoreEq (reference entry 14) (MycpuRegisterSequence.returned entry) := by
  intro r outside
  by_cases h1 : r = .x1
  · subst r; rw [MycpuRegisterSequence.saved_ra, reference_ra]
  by_cases h2 : r = .x2
  · subst r; rw [MycpuRegisterSequence.saved_sp, reference_final_sp]
  by_cases h8 : r = .x8
  · subst r; rw [MycpuRegisterSequence.saved_s0, reference_final_s0]
  by_cases h10 : r = .x10
  · subst r; rw [MycpuRegisterSequence.result, reference_final_result entry entryPC]
  by_cases h15 : r = .x15
  · subst r
    simp [MycpuRegisterSequence.returned, MycpuRegisterSequence.popped, MycpuRegisterSequence.restored,
      MycpuRegisterSequence.computed, MycpuRegisterSequence.framed, MycpuRegisterSequence.pushed,
      MycpuScalar.addressCalc, MycpuScalar.offsetCalc, MycpuScalar.after, MycpuMemory.after,
      MycpuReturn.after, MachCSL.Sail.Registers.write]
    rw [show sign_extend (m := 64) 0#12 = 0#64 from rfl, BitVec.add_zero]
  have hnpc : r ≠ .nextPC := by simp only [ignored, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside; exact outside.2.1
  have hpc : r ≠ .PC := by simp only [ignored, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside; exact outside.1
  have hinc : r ≠ .minstret_increment := by simp only [ignored, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside; exact outside.2.2.1
  rw [reference_other entry 14 r hpc (by simp [bodyWrites, hnpc, hinc, h1, h2, h8, h10, h15])]
  simp [MycpuRegisterSequence.returned, MycpuRegisterSequence.popped, MycpuRegisterSequence.restored,
    MycpuRegisterSequence.computed, MycpuRegisterSequence.framed, MycpuRegisterSequence.pushed,
    MycpuScalar.addressCalc, MycpuScalar.offsetCalc, MycpuScalar.after, MycpuMemory.after,
    MycpuReturn.after, MachCSL.Sail.Registers.write, Ne.symm h1, Ne.symm h2, Ne.symm h8,
    Ne.symm h10, Ne.symm h15, Ne.symm hnpc, Ne.symm hpc]

end Xv6.Kernel.MycpuBare
