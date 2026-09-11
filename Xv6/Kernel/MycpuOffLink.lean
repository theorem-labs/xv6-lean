import Xv6.Kernel.MycpuOffProofs
import Xv6.Kernel.MycpuBareLink
import MachCSL.Logic.SupervisorBitsProofs
import MachCSL.Logic.SupervisorBitsRegistry

namespace Xv6.Kernel.MycpuOff
open Iris MachCSL.Machine MachCSL.Logic

/-- Both resource and fourteen-cycle dependencies are supplied by the existing
native implementations, with the same physical register capacity. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity :=
  actual capacity (SupervisorBits.actual capacity.supervisorBits) (MycpuBare.nativeSpec capacity.machine)

/-- Reuse the existing complete machine registry and BitVec1 camera at 44. -/
def registryCapacity : Capacity SupervisorBits.registry :=
  ⟨SupervisorBits.machineCapacity, SupervisorBits.nativeCapacity.bits⟩

theorem registry_machine : registryCapacity.machine = SupervisorBits.machineCapacity := rfl
theorem registry_bits : registryCapacity.supervisorBits = SupervisorBits.nativeCapacity := rfl

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc SupervisorBits.registry] :
    Spec registryCapacity := nativeSpec registryCapacity

end Xv6.Kernel.MycpuOff
