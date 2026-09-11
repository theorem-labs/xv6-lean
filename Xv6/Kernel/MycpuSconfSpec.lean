import Xv6.Kernel.MycpuSconfDefs

namespace Xv6.Kernel.MycpuSconf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

structure PureSpec : Prop where
  bare_tier : ∀ tier, MycpuRegimeShell.Admits .bare tier → tier = .identity
  bare_result : ∀ cpu original after, MycpuBareSource.Result cpu original after → Result cpu original after
  kpt_result : ∀ cpu original after, MycpuKptSource.Result cpu original after → Result cpu original after

/-- Actual source body theorem for either tier and either permitted slot.
No branch selection, opened packet, Config, physical words, component WP,
execution witness or success fact is a caller premise. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  function : ∀ image fixed whole gen era cpu tier ξ original available tick extra post,
    2 ≤ available →
    iprop(⊢ input capacity fixed gen era cpu tier ξ original available extra -∗
      finish capacity image fixed whole gen era cpu tier ξ original available extra post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post)

end Xv6.Kernel.MycpuSconf
