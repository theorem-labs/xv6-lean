import MachCSL.Logic.EventWPJalLoopProofs
import MachCSL.Logic.EventWPJalLink
import MachCSL.Logic.RestartWPLink

namespace MachCSL.Logic.EventWPJal
open Iris Iris.BI MachCSL.Machine

/-- Both callee WP contracts are supplied at the same concrete 23-slot registry.
The source's broader arbitrary-preboot PMP family remains a separate bridge. -/
theorem registryJalLoopWPSpec [Platform] (names : Invariant.Names) :
    letI := UartGhost.nativeInvariant names
    JalLoopWPSpec UartGhost.machineCapacity := by
  letI := UartGhost.nativeInvariant names
  exact jalLoopWPSpec UartGhost.machineCapacity
    (registryJalCycleWPSpec names) (RestartWP.registryRestartWPSpec names)

end MachCSL.Logic.EventWPJal
