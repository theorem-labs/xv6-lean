import MachCSL.Logic.RegisterDefs
import MachCSL.Machine.State
import Init.Data.List.FinRange

/-! The source per-hart register bridge, over the actual complete eight-CPU set. -/
namespace MachCSL.Logic.GlobalRegisters
open Iris Iris.BI MachCSL.Machine

abbrev CPUSet := _root_.Std.ExtTreeSet CPU
abbrev Names := CPU → GName
abbrev Files := CPU → RegisterFile

def allCPUs : CPUSet := _root_.Std.ExtTreeSet.ofList (List.finRange 8)

theorem mem_allCPUs (cpu : CPU) : cpu ∈ allCPUs := by
  simp only [allCPUs, _root_.Std.ExtTreeSet.mem_ofList, List.contains_iff_mem]
  exact List.mem_finRange cpu

variable {GF : BundledGFunctors} (capacity : Registers.Capacity GF)

/-- Exact `gregs_interp` / `gregs_interp_at` shape, with explicit name function. -/
def gregsInterp (names : Names) (files : Files) : IProp GF :=
  iprop([∗set] cpu ∈ allCPUs, Registers.regInterpAt capacity (names cpu) (files cpu))

/-- Complete initial ownership for each hart, separate from its state bridge. -/
def allInitialCells (names : Names) (files : Files) : IProp GF :=
  iprop([∗set] cpu ∈ allCPUs, Registers.initialCells capacity (names cpu) (files cpu))

end MachCSL.Logic.GlobalRegisters
