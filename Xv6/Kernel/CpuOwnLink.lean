import Xv6.Kernel.CpuOwnProofs
import Xv6.Kernel.MycpuRegimeShellLink

namespace Xv6.Kernel.CpuOwn
open Iris MachCSL.Logic

/-- Existing capacities at the actual source names; no camera or ghost
name allocation, nor any claim that the boot premises have been installed. -/
def registryCapacity : Capacity KptGhost.registry :=
  ⟨MycpuRegimeShell.registryCapacity,KptGhost.heldSetCapacity⟩

theorem registry_execution_same : registryCapacity.execution = MycpuRegimeShell.registryCapacity := rfl
theorem registry_machine_same : registryCapacity.machine = KptGhost.machineCapacity := rfl
theorem registry_bits_same : registryCapacity.execution.supervisorBits = KptGhost.supervisorCapacity := rfl
theorem registry_held_same : registryCapacity.heldSets = KptGhost.heldSetCapacity := rfl
theorem registry_held_slot : registryCapacity.heldSets.set.τ = 26 := rfl

theorem nativePureSpec : PureSpec := pureSpec

/-- All resource contracts are implemented from the existing native
byte/register/bit/held-set cameras. No supplied component Spec remains. -/
theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec : Spec registryCapacity := nativeSpec _

end Xv6.Kernel.CpuOwn
