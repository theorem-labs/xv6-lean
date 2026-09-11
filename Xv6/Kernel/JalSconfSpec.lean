import Xv6.Kernel.JalSconfDefs

namespace Xv6.Kernel.JalSconf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

/-- No tier or slot is chosen by the caller. Identity examines its actual
slot; full tier's admissibility excludes Bare. No stack minimum is needed. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  cycle : ∀ image fixed whole gen era cpu tier ξ file available pc imm tick extra post,
    KptJal.TargetEven pc imm →
    iprop(⊢ input capacity fixed gen era cpu tier ξ file available pc imm extra -∗
      finish capacity image fixed whole gen era cpu tier ξ file available pc imm extra post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post)

end Xv6.Kernel.JalSconf
