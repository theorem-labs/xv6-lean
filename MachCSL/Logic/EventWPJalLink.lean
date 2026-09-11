import MachCSL.Logic.EventWPJalProofs
import MachCSL.Logic.EventWPLink
import MachCSL.Logic.UartGhostRegistry

namespace MachCSL.Logic.EventWPJal
open Iris Iris.BI MachCSL.Machine

/-- Concrete native-Iris linkage at the common 23-slot UART/PLIC registry.
It retains the explicit snapshot precondition and pure-node continuation;
it is not the closed all-power-on loop gate. -/
theorem registryJalCycleWPSpec [Platform] (names : Invariant.Names) :
    letI := UartGhost.nativeInvariant names
    JalCycleWPSpec UartGhost.machineCapacity := by
  letI := UartGhost.nativeInvariant names
  exact jalCycleWPSpec UartGhost.machineCapacity
    (EventWP.eventWPSpec EventWP.initialMapFacts UartGhost.machineCapacity
      (RegisterWP.registerWPSpec UartGhost.machineCapacity)
      (MemoryReadWP.memoryReadWPSpec UartGhost.machineCapacity))

end MachCSL.Logic.EventWPJal
