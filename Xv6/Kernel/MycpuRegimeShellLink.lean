import Xv6.Kernel.MycpuRegimeShellProofs
import Xv6.Kernel.KptOwnershipLink
import MachCSL.Logic.SupervisorBitsProofs

namespace Xv6.Kernel.MycpuRegimeShell
open Iris MachCSL.Machine MachCSL.Logic

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity :=
  actual capacity (SupervisorBits.actual capacity.supervisorBits)

/-- The same existing machine and slots44–47; no additional camera. -/
def registryCapacity : Capacity KptGhost.registry :=
  ⟨KptOwnership.registryCapacity, KptGhost.supervisorCapacity.bits⟩

theorem registry_machine_same : registryCapacity.machine = KptGhost.machineCapacity := rfl
theorem registry_bits_same : registryCapacity.supervisorBits = KptGhost.supervisorCapacity := rfl
theorem registry_translation_same : registryCapacity.translation = KptOwnership.registryCapacity := rfl

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] : Spec registryCapacity :=
  nativeSpec registryCapacity

end Xv6.Kernel.MycpuRegimeShell
