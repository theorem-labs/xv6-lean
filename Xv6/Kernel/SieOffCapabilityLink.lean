import Xv6.Kernel.SieOffCapabilityProofs

namespace Xv6.Kernel.SieOffCapability
open Iris

/-- Every disabled source capability law is implemented by actual native
component ownership, preserving the same machine and runtime ghost names. -/
theorem nativeSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity where
  witness_persistent := witness_persistent capacity
  witness_identity := witness_identity capacity
  witness_receipt := witness_receipt capacity
  intro := intro_cap capacity
  intro_bare := intro_bare capacity
  open_cap := open_cap capacity
  witness_access := witness_access capacity
  timer_access := timer_access capacity
  tier_up := tier_up capacity
  retarget := retarget capacity
  push := push capacity
  pop := pop capacity
  grow := grow capacity
  shrink := shrink capacity
  two_words := two_words capacity
  gpr_open := gpr_open capacity
  gpr_intro := gpr_intro capacity
  gpr_at_open := gpr_at_open capacity
  gpr_at_close := gpr_at_close capacity

theorem registrySpec {hlc : HasLC} [InvGS_gen hlc MachCSL.Logic.KptGhost.registry] :
    Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.SieOffCapability
