import MachCSL.Logic.JalBootHandlerProofs
import MachCSL.Logic.EventWPJalUniversalLink
import MachCSL.Logic.UartWPLink
import MachCSL.Logic.PlicWPLink
import MachCSL.Logic.ResetDiskWPProofs

namespace MachCSL.Logic.JalBootHandler
open Iris Iris.BI MachCSL.Machine

/-- Discharge every worker contract at the shared registry, in the native
invariant world supplied by the caller (in particular, by strong adequacy). -/
theorem registry_boot_handler [Platform] {hlc : HasLC} [InvGS_gen hlc UartGhost.registry]
    (ns : Namespaces) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (template : Era.Record) :
    iprop(⊢ ObservationInvariant.trivial UartGhost.machineCapacity.power ns.observations fixed.observations -∗
      PowerWP.bootHandler UartGhost.machineCapacity jalImage fixed whole template) := by
  apply boot_handler UartGhost.machineCapacity UartGhost.registryCapacity ns
  · exact EventWPJal.universalJalWPSpec UartGhost.machineCapacity
      (EventWP.eventWPSpec EventWP.initialMapFacts UartGhost.machineCapacity
        (RegisterWP.registerWPSpec UartGhost.machineCapacity)
        (MemoryReadWP.memoryReadWPSpec UartGhost.machineCapacity))
      (RestartWP.restartWPSpec UartGhost.machineCapacity)
  · exact UartWP.uartWPSpec UartGhost.machineCapacity UartGhost.registryCapacity
  · exact PlicWP.plicWPSpec UartGhost.machineCapacity
  · exact ResetDiskWP.resetDiskWPSpec UartGhost.machineCapacity

end MachCSL.Logic.JalBootHandler
