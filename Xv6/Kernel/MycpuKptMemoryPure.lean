import Xv6.Kernel.MycpuKptMemorySpec
import Xv6.Kernel.MycpuMemoryPlan
import Xv6.Kernel.MycpuRegimeShellPlan

namespace Xv6.Kernel.MycpuKptMemory
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 10000

theorem store_body [Platform] (slot : Slot) : body .store slot =
    execute_STORE (MycpuMemory.immediate slot) (MycpuMemory.dataIndex slot) (.Regidx 2#5) 8 :=
  MycpuMemory.store_body_eq slot

theorem load_body [Platform] (slot : Slot) : body .load slot =
    execute_LOAD (MycpuMemory.immediate slot) (.Regidx 2#5) (MycpuMemory.dataIndex slot) false 8 :=
  MycpuMemory.load_body_eq slot

theorem store_false : storeTail (.Ok false) = pure (.Retire_Success ()) := rfl
theorem store_error (error : ExecutionResult) : storeTail (.Err error) = pure error := rfl
theorem load_error (slot : Slot) (error : ExecutionResult) : loadTail slot (.Err error) = pure error := rfl

theorem footprint_unique (shares : Shares) (slot : Slot) : RegisterFootprint.Unique (footprint shares slot) := by
  have keys : (footprint shares slot).map Prod.fst =
      (footprint MycpuRegimeShell.sourceShares slot).map Prod.fst := rfl
  unfold RegisterFootprint.Unique
  rw [keys]
  cases slot <;> decide

theorem footprint_counts (shares : Shares) (slot : Slot) :
    (footprint shares slot).length = 7 ∧ (remainderFootprint shares slot).length = 43 := by
  cases slot <;> exact ⟨rfl, rfl⟩

theorem footprint_members (shares : Shares) (slot : Slot) (cell : Register × DFrac)
    (member : cell ∈ footprint shares slot) : cell ∈ MycpuRegimeShell.footprint shares := by
  cases slot <;>
    simp only [footprint, memoryShares, KptAddress.auxiliaryFootprint, MycpuMemory.dataRegister,
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
    entry control cpu (afterMap .load slot values word) = MycpuMemory.after slot (entry control cpu values) word := by
  funext r
  cases slot <;> cases r <;> rfl

theorem after_zero (kind : Kind) (slot : Slot) (values : HartTp.GprFile) (word : BitVec 64) :
    afterMap kind slot values word 0#5 = values 0#5 := by
  apply map_other
  cases slot <;> decide

end Xv6.Kernel.MycpuKptMemory
