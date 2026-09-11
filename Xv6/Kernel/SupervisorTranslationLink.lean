import Xv6.Kernel.SupervisorTranslationProofs
import Xv6.Kernel.KptOwnershipLink

namespace Xv6.Kernel.SupervisorTranslation
open Iris MachCSL.Logic

/-- All source one-shot and arm-resource laws are discharged natively.
The InvGS world and all old camera identities are supplied unchanged. -/
theorem nativeSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity where
  pending_timeless := pending_timeless capacity
  shot_timeless := shot_timeless capacity
  on_timeless := on_timeless capacity
  on_persistent := on_persistent capacity
  allocate := allocate capacity
  allocate_fresh := allocate_fresh capacity
  halves := halves capacity
  flip := flip capacity
  receipt := receipt capacity
  on_pending_false := on_pending_false capacity
  pending_shot_false := pending_shot_false capacity
  shot_exclusive := shot_exclusive capacity
  bare_intro := bare_intro capacity
  bare_access := bare_access capacity
  intro_bare := intro_bare capacity
  intro_kpt := intro_kpt capacity
  access_bare := access_bare capacity
  access_kpt := access_kpt capacity

theorem registrySpec {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec _

end Xv6.Kernel.SupervisorTranslation
