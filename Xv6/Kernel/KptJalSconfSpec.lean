import Xv6.Kernel.KptJalSconfDefs

namespace Xv6.Kernel.KptJalSconf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

structure PureSpec : Prop where
  stack : ∀ pc file, SieOffCapability.sp (afterFile pc file) = SieOffCapability.sp file
  saved : ∀ pc file, MycpuOff.Saved file (afterFile pc file)
  boundary : ∀ pc imm initial after,
    SieOffPacket.Boundary pc initial →
    MycpuRegimeShell.Completed (KptJal.afterControl pc imm (KptJal.started initial)) after →
    SieOffPacket.Boundary (KptJal.target pc imm) after

/-- No free-stack lower bound is necessary for the JAL itself. Source input
and actual code derive its owned configuration and encodability internally. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  cycle : ∀ image fixed whole gen era cpu ξ file available pc imm tick (frame : IProp GF) post,
    KptJal.TargetEven pc imm →
    iprop(⊢ input capacity fixed gen era cpu ξ file available pc imm frame -∗
      finish capacity image fixed whole gen era cpu ξ file available pc imm frame post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post)

end Xv6.Kernel.KptJalSconf
