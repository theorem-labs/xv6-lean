import MachCSL.Logic.EventWPProofs
import MachCSL.Logic.RegisterWPLink
import MachCSL.Logic.MemoryReadWPLink
import MachCSL.Logic.RegisterLink

namespace MachCSL.Logic.EventWP
open Iris Iris.BI MachCSL.Machine

theorem initialMapFacts : InitialMapFacts := ⟨Registers.initialMap_lookup⟩

/-- Concrete native-Iris rule linkage; no callee WP implementation is assumed. -/
theorem registryEventWPSpec [Platform] (names : Invariant.Names) :
    letI := names.native Invariant.registryCapacity
    EventWPSpec Invariant.machineCapacity := by
  letI := names.native Invariant.registryCapacity
  exact eventWPSpec initialMapFacts Invariant.machineCapacity
    (RegisterWP.registryRegisterWPSpec names) (MemoryReadWP.registryMemoryReadWPSpec names)

end MachCSL.Logic.EventWP
