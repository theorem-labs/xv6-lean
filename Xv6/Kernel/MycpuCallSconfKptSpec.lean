import Xv6.Kernel.MycpuCallSconfKptDefs

namespace Xv6.Kernel.MycpuCallSconfKpt
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  targetEven : ∀ pc imm, KptJal.target pc imm = MycpuSconfKpt.entryPC → KptJal.TargetEven pc imm
  returnPC : ∀ cpu pc original, is_aligned_vaddr (.Virtaddr pc) 2 = true →
    MycpuSconfKpt.returnPC cpu (KptJal.afterValues pc original) = KptJal.link pc
  result : ∀ cpu pc original after, Result cpu (KptJal.afterValues pc original) after →
    Result cpu original after

/-- Actual JAL-x1 call followed by all fourteen function cycles. All source
resources are restored at PC+4; only the genuine final continuation is given. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  call : ∀ image fixed whole gen era cpu ξ original available pc imm tick (frame : IProp GF) post,
    2 ≤ available → KptJal.target pc imm = MycpuSconfKpt.entryPC →
    iprop(⊢ input capacity fixed gen era cpu ξ original available pc imm frame -∗
      finish capacity image fixed whole gen era cpu ξ original available pc imm frame post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post)

end Xv6.Kernel.MycpuCallSconfKpt
