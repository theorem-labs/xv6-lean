import Xv6.Kernel.KptJalSourceDefs

namespace Xv6.Kernel.KptJalSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

structure PureSpec : Prop where
  stack : ∀ pc file, SieOffCapability.sp (afterFile pc file) = SieOffCapability.sp file
  saved : ∀ pc file, MycpuOff.Saved file (afterFile pc file)
  boundary : ∀ pc imm initial after, SieOffPacket.Boundary pc initial →
    MycpuRegimeShell.Completed (KptJal.afterControl pc imm (KptJal.started initial)) after →
    SieOffPacket.Boundary (KptJal.target pc imm) after

/-- Exact branch rule for either source tier. TargetEven is the only
additional pure premise; code supplies PC alignment. No minimum stack depth
or known fetch/translation success is assumed. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  cycle : ∀ image fixed whole gen era cpu tier ξ file available pc imm tick extra post,
    KptJal.TargetEven pc imm →
    iprop(⊢ input capacity fixed gen era cpu tier ξ file available pc imm extra -∗
      finish capacity image fixed whole gen era cpu tier ξ file available pc imm extra post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post)

end Xv6.Kernel.KptJalSource
