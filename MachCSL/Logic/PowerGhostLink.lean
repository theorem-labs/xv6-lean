import MachCSL.Logic.PowerGhostProofs
import MachCSL.Logic.PowerGhostRegistry
import MachCSL.Logic.ReservationLink
import MachCSL.Logic.GlobalRegistersLink

/-! Fixed-component linking with the preceding proved resource contracts. -/
namespace MachCSL.Logic.PowerGhost

theorem registryPowerGhostSpec : PowerGhostSpec registryCapacity := powerGhostSpec registryCapacity
theorem registryGlobalRegisterSpec : GlobalRegisters.GlobalRegisterSpec registerCapacity :=
  GlobalRegisters.globalRegisterSpec registerCapacity (Registers.registerSpec registerCapacity)

end MachCSL.Logic.PowerGhost
