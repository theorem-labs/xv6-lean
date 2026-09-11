import MachCSL.Logic.UartGhostProofs
import MachCSL.Logic.UartGhostRegistry
import MachCSL.Devices.Plic.Plan

namespace MachCSL.Logic.UartGhost

theorem registryUartGhostSpec : UartGhostSpec registryCapacity := uartGhostSpec registryCapacity

end MachCSL.Logic.UartGhost
