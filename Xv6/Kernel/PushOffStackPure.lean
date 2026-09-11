import Xv6.Kernel.PushOffStackSpec
import Xv6.Kernel.MycpuMemoryPlan
import Xv6.Kernel.MycpuRegimeShellPlan

namespace Xv6.Kernel.PushOffStack
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 10000

theorem store_body [Platform] (slot : Slot) : body .store slot =
    execute_STORE (immediate slot) (regidx slot) (.Regidx 2#5) 8 := by
  cases slot <;> rfl

theorem load_body [Platform] (slot : Slot) : body .load slot =
    execute_LOAD (immediate slot) (.Regidx 2#5) (regidx slot) false 8 := by
  cases slot <;> rfl

theorem store_false : storeTail (.Ok false) = pure (.Retire_Success ()) := rfl
theorem store_error (error : ExecutionResult) : storeTail (.Err error) = pure error := rfl
theorem load_error (slot : Slot) (error : ExecutionResult) : loadTail slot (.Err error) = pure error := rfl

theorem footprint_unique (shares : Shares) (slot : Slot) : RegisterFootprint.Unique (footprint shares slot) := by
  have keys : (footprint shares slot).map Prod.fst =
      (footprint MycpuRegimeShell.sourceShares slot).map Prod.fst := rfl
  unfold RegisterFootprint.Unique
  rw [keys]
  cases slot <;> decide

theorem bare_footprint_unique (s : Shares) (slot : Slot) : RegisterFootprint.Unique (bareFootprint s slot) := by
  have keys : (bareFootprint s slot).map Prod.fst = (bareFootprint MycpuRegimeShell.sourceShares slot).map Prod.fst := rfl
  unfold RegisterFootprint.Unique
  rw [keys]
  cases slot <;> decide

theorem footprint_counts (shares : Shares) (slot : Slot) :
    (footprint shares slot).length = 7 ∧ (bareFootprint shares slot).length = 10 ∧
      (remainderFootprint shares slot).length = 43 := by
  cases slot <;> exact ⟨rfl,rfl,rfl⟩

theorem footprint_members (shares : Shares) (slot : Slot) (cell : Register × DFrac)
    (member : cell ∈ footprint shares slot) : cell ∈ MycpuRegimeShell.footprint shares := by
  cases slot <;>
    simp only [footprint, memoryShares, MycpuKptMemory.memoryShares, KptAddress.auxiliaryFootprint, register,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with (rfl | rfl | rfl | rfl | rfl) | rfl | rfl
  all_goals simp [MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint,
    show MycpuRegimeShell.gprFootprint = MycpuOff.gprFootprint from rfl, MycpuOff.gpr_list]

theorem ambient (control : RegisterFile) (cpu : CPU) (values : HartTp.GprFile)
    (config : Config control) (facts : SupervisorBits.MsFacts (control .mstatus)) :
    KptMemory.Ambient (entry control cpu values) := by
  exact ⟨⟨config.privilege, facts.2.1, config.pma, config.htif⟩,
    MycpuOff.bit_ne_one_eq_zero _ facts.1, of_decide_eq_true facts.2.2.1, config.pmm, config.adue⟩

theorem map_other (kind : Kind) (slot : Slot) (values : HartTp.GprFile) (old : BitVec 64)
    (i : HartTp.Index) (different : i ≠ index slot) : afterMap kind slot values old i = values i := by
  cases kind with
  | store => rfl
  | load => exact HartTp.set_other values (index slot) i old different

theorem after_sp (kind : Kind) (slot : Slot) (cpu : CPU) (values : HartTp.GprFile) (old : BitVec 64) :
    HartTp.rget cpu (afterMap kind slot values old) 2#5 = HartTp.rget cpu values 2#5 := by
  change afterMap kind slot values old 2#5 = values 2#5
  apply map_other
  cases slot <;> decide

theorem after_address (kind : Kind) (slot : Slot) (cpu : CPU) (values : HartTp.GprFile)
    (old : BitVec 64) (other : Slot) :
    address cpu (afterMap kind slot values old) other = address cpu values other := by
  simp only [address, after_sp]

theorem entry_load (control : RegisterFile) (cpu : CPU) (values : HartTp.GprFile) (slot : Slot) (word : BitVec 64) :
    entry control cpu (afterMap .load slot values word) = physicalAfter .load slot (entry control cpu values) word := by
  funext r
  cases slot <;> cases r <;> rfl

theorem after_zero (kind : Kind) (slot : Slot) (values : HartTp.GprFile) (word : BitVec 64) :
    afterMap kind slot values word 0#5 = values 0#5 := by
  apply map_other
  cases slot <;> decide

theorem entry_after kind slot control cpu values word :
    entry control cpu (afterMap kind slot values word) = physicalAfter kind slot (entry control cpu values) word := by
  cases kind
  · exact entry_load control cpu values slot word
  · rfl

theorem immediate_eq slot : sign_extend (m := 64) (immediate slot) = offset slot := by cases slot <;> rfl

theorem inventory : [instructionIndex .store .ra, instructionIndex .store .s0, instructionIndex .store .s1,
    instructionIndex .load .ra, instructionIndex .load .s0, instructionIndex .load .s1].map Fin.val = [1,2,3,14,15,16] := rfl

theorem anchored cpu values entrySP slot (ready : StackReady cpu values entrySP) :
    address cpu values slot = KernelStack.paStk entrySP (ordinal slot) := by
  unfold address
  rw [ready]
  cases slot <;> simp [offset, ordinal, KernelStack.paStk, StackPhysical.paStk, BitVec.sub_eq_add_neg, BitVec.add_assoc]

end Xv6.Kernel.PushOffStack
