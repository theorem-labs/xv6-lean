import Xv6.Kernel.Sv39TreeWalkProofs

namespace Xv6.Kernel.Sv39TreeWalk
open Iris MachCSL.Machine MachCSL.Logic

/-- Both node and whole-tree contracts use actual pinned reads, universal
raw-word validation and the native kernel-leaf rule. No shared accessor or
caller-supplied execution specification remains as an input. -/
theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity := actual capacity

end Xv6.Kernel.Sv39TreeWalk
