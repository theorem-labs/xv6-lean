import Xv6.Kernel.PushOffWord4BareDefs
namespace Xv6.Kernel.PushOffWord4Bare
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
structure PureSpec [Platform] : Prop where
  footprintUnique : ∀ s, RegisterFootprint.Unique (footprint s)
  transform : ∀ s rs, Config rs → ∀ va kind,
    RegisterPlan.Returns (footprint s) rs (SupervisorAddress.program va kind) (.Virtaddr va) rs
  read : ∀ s rs, Config rs → ∀ va, KernelDatumWord4.Aligned va → SupervisorPhysical.RamRange va 4 →
    SupervisorFetchRead.OneRead (footprint s) rs va 4 (addressProgram .load va 0#32) (fun word => .Ok word)
  write : ∀ s rs, Config rs → ∀ va new, KernelDatumWord4.Aligned va → SupervisorPhysical.RamRange va 4 →
    SupervisorWrite4.OneWrite (footprint s) rs va new (addressProgram .store va new) (fun success => .Ok success)

/-- Internal physical-window rule; the public body rule supplies all of its
geometry and window resources by accessing the actual virtual word. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Prop where
  transformed : ∀ s rs, Config rs → ∀ kind ξ va dq old new rr,
    KernelDatumWord4.Aligned va → SupervisorPhysical.RamRange va 4 →
    (kind = .store → dq = .own 1) → ∀ image fixed whole gen era cpu continuation post,
    iprop(⊢ MachineInterp.generationCertificate capacity fixed gen era -∗
      cells capacity era cpu rs s -∗ TsoContextReadWP.running capacity era cpu ξ -∗
      TsoContextBytesReadWP.window capacity era ξ va 4 dq old -∗
      Reservations.resvFrag capacity.era.reservations era.reservations cpu rr -∗
      finish capacity image fixed whole gen era cpu rs s kind ξ va dq old new rr continuation post -∗
      RegisterWP.threadWP capacity image fixed whole
        (.hart gen cpu (program kind va new >>= continuation)) post)
end Xv6.Kernel.PushOffWord4Bare
