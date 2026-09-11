import MachCSL.Logic.EventPlanProofs
import MachCSL.Logic.EventPlanCombinators
import MachCSL.Logic.RegisterWPProofs
import MachCSL.Logic.MemoryReadWPProofs
import MachCSL.Logic.MemoryWriteWPLink
import MachCSL.Logic.BarrierWPProofs
import MachCSL.Logic.RegisterLink

namespace MachCSL.Logic.EventPlan
open Iris Iris.BI MachCSL.Machine

/-- Every event-rule premise is discharged by its existing native-Iris proof. -/
theorem nativeContracts {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Contracts capacity where
  registers := RegisterWP.registerWPSpec capacity
  plain := MemoryReadWP.memoryReadWPSpec capacity
  exclusive := MemoryExclusiveWP.memoryExclusiveWPSpec capacity
  write := MemoryWriteWP.nativeMemoryWriteWPSpec capacity
  barrier := BarrierWP.barrierWPSpec capacity

theorem nativeEventPlanSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : EventPlanSpec capacity :=
  eventPlanSpec ⟨Registers.initialMap_lookup⟩ capacity (nativeContracts capacity)

/-- Same shared machine registry and invariant world; no new camera or name. -/
theorem registryEventPlanSpec [Platform] (names : Invariant.Names) :
    letI := FsLink.nativeInvariant names
    EventPlanSpec FsLink.machineCapacity := by
  letI := FsLink.nativeInvariant names
  exact nativeEventPlanSpec FsLink.machineCapacity

end MachCSL.Logic.EventPlan
