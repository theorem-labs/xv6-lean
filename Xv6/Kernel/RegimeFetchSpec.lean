import Xv6.Kernel.RegimeFetchDefs
namespace Xv6.Kernel.RegimeFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  guardsMono : ∀ regime control cpu values result (left right : Trace regime → IProp GF),
    iprop(⊢ (∀ trace, left trace -∗ right trace) -∗
      guards regime control cpu values result left -∗ guards regime control cpu values result right)
  fetch : ∀ regime control values, Config control → ∀ tier result ξ rr,
    MycpuRegimeShell.Admits regime tier →
    ∀ image fixed whole gen era cpu (frame : IProp GF) continuation post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu regime control values -∗ code capacity era tier (control .PC) result -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu regime control values tier result ξ rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post)
end Xv6.Kernel.RegimeFetch
