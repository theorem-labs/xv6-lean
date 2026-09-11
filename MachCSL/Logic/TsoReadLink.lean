import MachCSL.Logic.TsoReadProofs
import MachCSL.Logic.InvariantLink

namespace MachCSL.Logic.TsoRead
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

/-- All view and pristine bridges instantiated at the existing twenty slots. -/
theorem registryTsoReadSpec : TsoReadSpec Invariant.machineCapacity :=
  tsoReadSpec Invariant.machineCapacity

end MachCSL.Logic.TsoRead
