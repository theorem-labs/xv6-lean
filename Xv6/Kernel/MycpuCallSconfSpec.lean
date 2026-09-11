import Xv6.Kernel.MycpuCallSconfDefs

namespace Xv6.Kernel.MycpuCallSconf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

/-- Actual JAL-x1 and all fourteen mycpu cycles. The only WP premise is
the genuine final continuation; no regime or successful execution is assumed. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  call : ∀ image fixed whole gen era cpu tier ξ original available pc imm tick extra post,
    2 ≤ available → KptJal.target pc imm = MycpuSconf.entryPC →
    iprop(⊢ input capacity fixed gen era cpu tier ξ original available pc imm extra -∗
      finish capacity image fixed whole gen era cpu tier ξ original available pc imm extra post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post)

end Xv6.Kernel.MycpuCallSconf
