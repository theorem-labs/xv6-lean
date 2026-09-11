import Xv6.Kernel.MycpuSconfKptDefs

namespace Xv6.Kernel.MycpuSconfKpt
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

structure PureSpec : Prop where
  result : ∀ initial original cpu after values, MycpuKpt.Result initial original cpu after values →
    Result cpu original values
  stack : ∀ initial original cpu after values, MycpuKpt.Result initial original cpu after values →
    MycpuKptEntry.sp values = MycpuKptEntry.sp original

/-- Only the genuine source post-return continuation is a WP input.
No explicit Config, root, native code windows, saved words, initial phase,
component WP, certificate or execution-success proof is supplied. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  function : ∀ image fixed whole gen era cpu ξ original available tick (frame : IProp GF) post,
    2 ≤ available →
    iprop(⊢ input capacity fixed gen era cpu ξ original available frame -∗
      finish capacity image fixed whole gen era cpu ξ original available frame post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post)

end Xv6.Kernel.MycpuSconfKpt
