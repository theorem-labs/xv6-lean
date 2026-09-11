import Xv6.Kernel.PushOffScalarSpec
import Xv6.Kernel.PushOffCodePureProofs
import Xv6.Kernel.MycpuReturnProofs

namespace Xv6.Kernel.PushOffScalar
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem inventory : ([Instruction.subSP,.framePointer,.saveStatus,.branchZero,.increment,
    .restoreSP,.returns,.shift,.mask,.jumpBack].map (fun i => (index i).val)) =
      [0,4,6,9,12,17,18,20,21,23] := rfl

theorem entry_set_2 control cpu values word :
 entry control cpu (HartTp.set values 2#5 word) = MachCSL.Sail.Registers.write (entry control cpu values) .x2 word := by
 funext r
 cases r <;> rfl
theorem entry_set_8 control cpu values word :
 entry control cpu (HartTp.set values 8#5 word) = MachCSL.Sail.Registers.write (entry control cpu values) .x8 word := by
 funext r
 cases r <;> rfl
theorem entry_set_9 control cpu values word :
 entry control cpu (HartTp.set values 9#5 word) = MachCSL.Sail.Registers.write (entry control cpu values) .x9 word := by
 funext r
 cases r <;> rfl
theorem entry_set_15 control cpu values word :
 entry control cpu (HartTp.set values 15#5 word) = MachCSL.Sail.Registers.write (entry control cpu values) .x15 word := by
 funext r
 cases r <;> rfl
theorem entry_nextPC control cpu values word :
    entry (MachCSL.Sail.Registers.write control .nextPC word) cpu values =
      MachCSL.Sail.Registers.write (entry control cpu values) .nextPC word := by
  funext r
  cases r <;> rfl

theorem after_entry (i : Instruction) control cpu values :
    entry (afterControl i control cpu values) cpu (afterValues i cpu values) =
      after i (entry control cpu values) := by
  cases i with
  | subSP | restoreSP => exact entry_set_2 control cpu values _
  | framePointer => exact entry_set_8 control cpu values _
  | saveStatus => exact entry_set_9 control cpu values _
  | increment | shift | mask => exact entry_set_15 control cpu values _
  | returns | jumpBack => exact entry_nextPC control cpu values _
  | branchZero =>
    change entry (if branchTaken cpu values then MachCSL.Sail.Registers.write control .nextPC (control .PC + 22#64) else control) cpu values =
      (if branchTaken cpu values then MachCSL.Sail.Registers.write (entry control cpu values) .nextPC (control .PC + 22#64) else entry control cpu values)
    split
    · exact entry_nextPC control cpu values _
    · rfl

theorem other (i : Instruction) cpu values key (different : destination i ≠ some key) :
    afterValues i cpu values key = values key := by
  cases i <;> simp only [destination, Option.some.injEq, ne_eq] at different
  all_goals simp [afterValues, HartTp.set, Ne.symm different]

theorem zero (i : Instruction) cpu values : afterValues i cpu values 0#5 = values 0#5 := by
  apply other
  cases i <;> decide

theorem pinned_tp (i : Instruction) cpu values :
    HartTp.rget cpu (afterValues i cpu values) HartTp.tp = HartTp.hartWord cpu := by
  simp [HartTp.rget, HartTp.pin, HartTp.set]

theorem control_other (i : Instruction) control cpu values r (different : r ≠ .nextPC) :
    afterControl i control cpu values r = control r := by
  cases i <;> simp [afterControl, MachCSL.Sail.Registers.write, Ne.symm different]
  split <;> simp [MachCSL.Sail.Registers.write, Ne.symm different]

theorem source_config (i : Instruction) control
    (misa : control .misa = 0x800000000014112d#64) (priv : control .cur_privilege = .Supervisor)
    (menv : control .menvcfg = 0xa000000000000000#64) (pc : control .PC = PushOffCode.pc (index i)) :
    Config i control := by
  cases i <;> try trivial
  · refine ⟨?_, ?_⟩
    · rw [misa]; rfl
    · rw [pc]; decide
  · exact MycpuReturn.source_config control ⟨priv,menv,misa⟩
  · refine ⟨?_, ?_⟩
    · rw [misa]; rfl
    · rw [pc]; decide

theorem branch_taken control cpu values (taken : branchTaken cpu values = true) :
    afterControl .branchZero control cpu values .nextPC = control .PC + 22#64 := by
  simp [afterControl,taken]

theorem branch_not_taken control cpu values (notTaken : branchTaken cpu values = false) :
    afterControl .branchZero control cpu values = control := by simp [afterControl,notTaken]

theorem jump_target control cpu values :
    afterControl .jumpBack control cpu values .nextPC = control .PC - 32#64 := by
  change control .PC + sign_extend (m := 64) 0x1fffe0#21 = _
  rw [show sign_extend (m := 64) 0x1fffe0#21 = -32#64 from rfl, BitVec.sub_eq_add_neg]

theorem return_target control cpu values :
    afterControl .returns control cpu values .nextPC = MycpuReturn.retPC (HartTp.rget cpu values 1#5) := rfl

/-- Addition by an even modular offset preserves the actual jump assertion. -/
theorem add_even (pc offset : BitVec 64) (hpc : Sail.BitVec.access pc 0 = 0#1)
    (hoff : offset.getLsbD 0 = false) : Sail.BitVec.access (pc + offset) 0 = 0#1 := by
  have low : pc.getLsbD 0 = false := by
    have h := congrArg (fun x : BitVec 1 => x.getLsbD 0) hpc
    simpa [Sail.BitVec.access,← BitVec.getLsbD_eq_getElem] using h
  simp [Sail.BitVec.access,← BitVec.getLsbD_eq_getElem,
    BitVec.getLsbD_add (by decide : 0 < 64),BitVec.carry_zero,low,hoff]

end Xv6.Kernel.PushOffScalar
