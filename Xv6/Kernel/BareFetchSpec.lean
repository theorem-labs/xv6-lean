import Xv6.Kernel.BareFetchDefs
namespace Xv6.Kernel.BareFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

/-- Actual full fetch from identity code ownership. A compressed fetch may
read a whole aligned word; the code predicate includes that exact footprint.
The result is determined by supplied bytes, without a successful-WP premise. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  fetch : ∀ shares rs, Config rs → ∀ result image fixed whole gen era cpu ξ continuation post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      cells capacity era cpu rs shares -∗ TsoContextBytesReadWP.running capacity.machine era cpu ξ -∗
      code capacity era (rs .PC) result -∗
      finish capacity image fixed whole gen era cpu ξ rs shares result continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post)
end Xv6.Kernel.BareFetch
