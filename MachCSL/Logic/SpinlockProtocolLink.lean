import MachCSL.Logic.SpinlockProtocolProofs
import MachCSL.Logic.FsTopLink

namespace MachCSL.Logic.SpinlockProtocol
open Iris MachCSL.Machine

/-- Reuse the actual lock product at slot 24, preserving the full 0–25 registry. -/
def registryCapacity : Capacity FsTop.registry :=
  ⟨FsTop.machineCapacity, FsTop.lockCapacity⟩

theorem registry_machine_same : registryCapacity.machine = FsTop.machineCapacity := rfl
theorem registry_lock_slot : registryCapacity.lock.lock.τ = 24 := rfl

/-- Native callbacks in the existing invariant world; no client callback assumptions. -/
theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc FsTop.registry] :
    SpinlockProtocolSpec registryCapacity := actual registryCapacity

end MachCSL.Logic.SpinlockProtocol
