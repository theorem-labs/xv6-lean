import Xv6.Kernel.RegimeFetchKptProofs
namespace Xv6.Kernel.RegimeFetch
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors}

theorem guards_mono regime control cpu values result (left right : Trace regime → IProp GF) :
    iprop(⊢ (∀ trace, left trace -∗ right trace) -∗
      guards regime control cpu values result left -∗ guards regime control cpu values result right) := by
  cases regime with
  | bare => exact BareJalFetch.guardReads_mono _ left right
  | kpt N root => exact KptFetch.guardChunks_mono _ _ _ left right

variable [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem wp_fetch regime control values (config : Config control) tier result ξ rr
    (admitted : MycpuRegimeShell.Admits regime tier) image fixed whole gen era cpu
    (frame : IProp GF) continuation post :
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu regime control values -∗ code capacity era tier (control .PC) result -∗
      TsoContextReadWP.running capacity.machine era cpu ξ -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu regime control values tier result ξ rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (program >>= continuation)) post) := by
  cases regime with
  | bare =>
    cases tier with
    | identity => exact wp_bare capacity control values config result ξ rr image fixed whole gen era cpu frame continuation post
    | full => contradiction
  | kpt N root => exact wp_kpt capacity control values config tier result ξ rr image fixed whole gen era cpu N root frame continuation post

theorem actual : Spec capacity := ⟨guards_mono,wp_fetch capacity⟩
end Xv6.Kernel.RegimeFetch
