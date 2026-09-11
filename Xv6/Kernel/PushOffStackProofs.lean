import Xv6.Kernel.PushOffStackBareProofs
import Xv6.Kernel.PushOffStackKptProofs

namespace Xv6.Kernel.PushOffStack
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem kpt_finish image fixed whole gen era cpu control values s kind slot tier ξ old rr frame continuation post N root :
    finish capacity image fixed whole gen era cpu (.kpt N root) control values s kind slot tier ξ old rr frame continuation post =
      Kpt.finish capacity image fixed whole gen era cpu control values s N root kind slot tier ξ (.own 1) old rr frame continuation post := by
  cases kind <;> rfl

theorem wp_body : ∀ s control values, Config control → ∀ regime tier,
    MycpuRegimeShell.Admits regime tier → ∀ kind slot ξ old rr,
    ∀ image fixed whole gen era cpu (frame : IProp GF) (continuation : ExecutionResult → SailM Unit) post,
    iprop(⊢ MachineInterp.generationCertificate capacity.machine fixed gen era -∗
      packet capacity era cpu regime control values s -∗ TsoContextReadWP.running capacity.machine era cpu ξ -∗
      KernelDatum.word capacity.translation era tier ξ (address cpu values slot) (.own 1) old -∗
      Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr -∗ frame -∗
      finish capacity image fixed whole gen era cpu regime control values s kind slot tier ξ old rr frame continuation post -∗
      RegisterWP.threadWP capacity.machine image fixed whole
        (.hart gen cpu (PushOffStack.body kind slot >>= continuation)) post) := by
  intro s control values config regime tier admits kind slot ξ old rr image fixed whole gen era cpu frame continuation post
  cases regime with
  | bare =>
    cases tier with
    | full => exact False.elim admits
    | identity => exact Bare.wp_body capacity s control values config kind slot ξ old rr image fixed whole gen era cpu frame continuation post
  | kpt N root =>
    rw [kpt_finish]
    exact Kpt.wp_body capacity s control values config kind slot tier ξ (.own 1) old rr (fun _ => rfl)
      image fixed whole gen era cpu N root frame continuation post

theorem actual : Spec capacity := ⟨wp_body capacity⟩

end Xv6.Kernel.PushOffStack
