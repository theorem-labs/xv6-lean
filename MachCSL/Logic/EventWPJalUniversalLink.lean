import MachCSL.Logic.EventWPJalUniversalProofs
import MachCSL.Logic.EventWPLink
import MachCSL.Logic.RestartWPLink

namespace MachCSL.Logic.EventWPJal
open Iris Iris.BI MachCSL.Machine

/-- Actual machine/cycle/restart implementations at the shared concrete 23-slot
registry. Runtime ownership is still an explicit precondition. -/
theorem registryUniversalJalWPSpec [Platform] (names : Invariant.Names) :
    letI := UartGhost.nativeInvariant names
    UniversalJalWPSpec UartGhost.machineCapacity := by
  letI := UartGhost.nativeInvariant names
  exact universalJalWPSpec UartGhost.machineCapacity
    (EventWP.eventWPSpec EventWP.initialMapFacts UartGhost.machineCapacity
      (RegisterWP.registerWPSpec UartGhost.machineCapacity)
      (MemoryReadWP.memoryReadWPSpec UartGhost.machineCapacity))
    (RestartWP.registryRestartWPSpec names)

/-- Direct specialization to every actual boot witness. All remaining premises
are the concrete resources the boot allocator must return to this hart. -/
theorem registry_boot_loop [Platform] (names : Invariant.Names)
    (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (generation : Nat) (era : Era.Record) (g : State) (facts : BootFacts jalImage g)
    (cpu : CPU) (dq : DFrac) (post : Empty → IProp UartGhost.registry) :
    letI := UartGhost.nativeInvariant names
    iprop(⊢ MachineInterp.generationCertificate UartGhost.machineCapacity fixed generation era -∗
      EventWP.ownedCells UartGhost.machineCapacity.era.registers (era.registers cpu) (g.registers cpu) -∗
      EventWP.codeResources UartGhost.machineCapacity era dq -∗
      Reservations.resvAny UartGhost.machineCapacity.era.reservations era.reservations cpu -∗
      RegisterWP.threadWP UartGhost.machineCapacity jalImage fixed whole (.hart generation cpu (.pure ())) post) := by
  letI := UartGhost.nativeInvariant names
  exact (registryUniversalJalWPSpec names).loop jalImage fixed whole generation era cpu
    (g.registers cpu) dq post (JalLoopPlan.bootFacts_family g facts cpu)

end MachCSL.Logic.EventWPJal
