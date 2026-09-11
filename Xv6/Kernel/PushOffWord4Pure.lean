import Xv6.Kernel.PushOffWord4Spec
import Xv6.Kernel.MycpuKptMemoryPure
import Xv6.Kernel.MycpuBareSourceEntry
namespace Xv6.Kernel.PushOffWord4
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 10000

theorem normalized (op : Op) : PushOffCode.normalized (index op) =
    match kind op with
    | .load => .LOAD (immediate op, .Regidx 10#5, .Regidx 15#5, false, 4)
    | .store => .STORE (immediate op, .Regidx 15#5, .Regidx 10#5, 4) := by
  cases op <;> rfl

theorem compressed [Platform] (op : Op) : execute (PushOffCode.decoded (index op)) =
    pure (.ExecuteAs (PushOffCode.normalized (index op))) := by cases op <;> rfl

theorem store_false : storeTail (.Ok false) = pure (.Retire_Success ()) := rfl
theorem store_error error : storeTail (.Err error) = pure error := rfl
theorem load_error error : loadTail (.Err error) = pure error := rfl

theorem footprint_unique (s : Shares) : RegisterFootprint.Unique (footprint s) := by
  simp [RegisterFootprint.Unique, footprint, KptAddress.auxiliaryFootprint]

theorem footprint_counts (s : Shares) : (footprint s).length = 7 ∧
    (remainderFootprint s).length = 43 ∧ (bareFootprint s).length = 10 := by
  exact ⟨rfl,rfl,rfl⟩

theorem footprint_members (s : Shares) (cell : Register × DFrac)
    (member : cell ∈ footprint s) : cell ∈ MycpuRegimeShell.footprint s := by
  simp only [footprint, memoryShares, KptAddress.auxiliaryFootprint,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl | rfl | rfl) | rfl | rfl <;>
    simp [MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint,
      show MycpuRegimeShell.gprFootprint = MycpuOff.gprFootprint from rfl, MycpuOff.gpr_list]

theorem kpt_ambient control cpu values N root (config : Config (.kpt N root) control)
    (facts : SupervisorBits.MsFacts (control .mstatus)) : KptMemory4.Ambient (entry control cpu values) :=
  ⟨⟨config.privilege,facts.2.1,config.pma,config.htif⟩,
    MycpuOff.bit_ne_one_eq_zero _ facts.1, of_decide_eq_true facts.2.2.1,
    config.pmm,config.adue N root rfl⟩

theorem bare_config control cpu values satp pmp (config : Config .bare control)
    (facts : SupervisorBits.MsFacts (control .mstatus))
    (mode : _get_Satp64_Mode (Mk_Satp64 satp) = 0#4)
    (tor : MachCSL.Machine.SupervisorPmp.TorRam pmp) :
    PushOffWord4Bare.Config (entry (MycpuBareSource.patch control satp pmp) cpu values) := by
  refine ⟨⟨config.privilege, MycpuOff.bit_ne_one_eq_zero _ facts.1,
    of_decide_eq_true facts.2.2.1, config.pmm, facts.2.1, ?_⟩, ?_, config.pma, config.htif⟩
  · change satpMode_of_bits .RV64 (_get_Satp64_Mode (Mk_Satp64 satp)) = some .Bare
    rw [mode]; rfl
  · exact ⟨tor.tor, tor.positive, tor.execute, tor.write, tor.read, tor.covers⟩

theorem map_other op values old i (different : i ≠ 15#5) : afterMap op values old i = values i := by
  cases op <;> first | rfl | exact HartTp.set_other values 15#5 i (old.signExtend 64) different

theorem after_address op cpu values old other :
    address cpu (afterMap op values old) other = address cpu values other := by
  unfold address
  change afterMap op values old 10#5 + _ = values 10#5 + _
  rw [map_other op values old 10#5 (by decide)]

theorem after_sp op cpu values old :
    HartTp.rget cpu (afterMap op values old) 2#5 = HartTp.rget cpu values 2#5 := by
  exact map_other op values old 2#5 (by decide)

theorem after_zero op values old : afterMap op values old 0#5 = values 0#5 :=
  map_other op values old 0#5 (by decide)

theorem entry_load control cpu values (old : BitVec 32) :
    entry control cpu (HartTp.set values 15#5 (old.signExtend 64)) =
      MachCSL.Sail.Registers.write (entry control cpu values) .x15 (old.signExtend 64) := by
  funext r; cases r <;> rfl
end Xv6.Kernel.PushOffWord4
