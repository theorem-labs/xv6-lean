import Xv6.Kernel.MycpuCallKptSourceDefs

namespace Xv6.Kernel.MycpuCallKptSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  targetEven : ∀ pc imm, KptJal.target pc imm = MycpuSconf.entryPC → KptJal.TargetEven pc imm
  returnPC : ∀ cpu pc original, is_aligned_vaddr (.Virtaddr pc) 2 = true →
    MycpuSconf.returnPC cpu (KptJal.afterValues pc original) = KptJal.link pc
  result : ∀ cpu pc original after, Result cpu (KptJal.afterValues pc original) after →
    Result cpu original after

/-- Actual JAL-x1 plus the complete native mycpu body, preserving the
original source tier. The only WP premise is the genuine final continuation. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  call : ∀ image fixed whole gen era cpu tier ξ original available pc imm tick extra post,
    2 ≤ available → KptJal.target pc imm = MycpuSconf.entryPC →
    iprop(⊢ input capacity fixed gen era cpu tier ξ original available pc imm extra -∗
      finish capacity image fixed whole gen era cpu tier ξ original available pc imm extra post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post)

end Xv6.Kernel.MycpuCallKptSource
