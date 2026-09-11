import Xv6.Kernel.KptOwnershipProofs
import MachCSL.Logic.KptGhostRegistry

namespace Xv6.Kernel.KptOwnership
open Iris MachCSL.Logic

/-- Reuse the existing 48-slot family; ownership adds no camera. -/
def registryCapacity : Capacity KptGhost.registry :=
  ⟨KptGhost.machineCapacity, KptGhost.kptCapacity.mapping,
    KptGhost.kptCapacity.tree, KptGhost.kptCapacity.bound⟩

theorem registry_machine_same : registryCapacity.machine = KptGhost.machineCapacity := rfl
theorem registry_ghost_same : registryCapacity.ghost = KptGhost.kptCapacity := rfl
theorem registry_views_same : registryCapacity.ghost.views = registryCapacity.machine.era.views := rfl

theorem registrySpec : Spec registryCapacity := nativeSpec registryCapacity

theorem nativeGeometrySpec : GeometrySpec := geometrySpec

end Xv6.Kernel.KptOwnership
