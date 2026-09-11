import MachCSL.Logic.GlobalRegistersProofs
import MachCSL.Logic.RegisterLink

/-! Only linking imports the per-hart proof implementation. No new slot is added. -/
namespace MachCSL.Logic.GlobalRegisters

theorem registryGlobalRegisterSpec : GlobalRegisterSpec Registers.registryCapacity :=
  globalRegisterSpec Registers.registryCapacity Registers.registryRegisterSpec

end MachCSL.Logic.GlobalRegisters
