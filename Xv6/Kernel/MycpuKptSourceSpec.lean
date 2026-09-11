import Xv6.Kernel.MycpuKptSourceDefs

namespace Xv6.Kernel.MycpuKptSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

/-- Opening and restoration are backed by actual resources. No per-step
Config, known save values, translated address, execution result or WP is input. -/
structure ResourceSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  save_area : ∀ era tier ξ entrySP available, 2 ≤ available →
    iprop(KernelStack.own capacity.translation era tier ξ entrySP available ⊣⊢
      ∃ saved : Words, MycpuKptBody.pair capacity era tier ξ entrySP saved ∗
        tail capacity era tier ξ entrySP available)
  open_entry : ∀ fixed gen era cpu tier ξ file available, 2 ≤ available →
    iprop(input capacity fixed gen era cpu tier ξ file available ⊢ ∃ root control saved rr,
      ⌜MycpuKptCycle.Config control⌝ ∗ ⌜SieOffPacket.Boundary entryPC control⌝ ∗
      resources capacity fixed gen era cpu tier ξ (sp file) available root control file saved rr)
  close_entry : ∀ fixed gen era cpu tier ξ entrySP available root control file saved rr returnPC,
    2 ≤ available → sp file = entrySP → SieOffPacket.Boundary returnPC control →
    iprop(resources capacity fixed gen era cpu tier ξ entrySP available root control file saved rr ⊢
      restored capacity fixed gen era cpu tier ξ file available returnPC)
  certificate : ∀ fixed gen era cpu tier ξ entrySP available root control file saved rr,
    iprop(resources capacity fixed gen era cpu tier ξ entrySP available root control file saved rr ⊢
      MachineInterp.generationCertificate capacity.machine fixed gen era ∗
      resources capacity fixed gen era cpu tier ξ entrySP available root control file saved rr)

end Xv6.Kernel.MycpuKptSource

namespace Xv6.Kernel.MycpuKptSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

/-- KPT branch for either original source tier; no caller native WP or configuration oracle. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  function : ∀ image fixed whole gen era cpu tier ξ original available tick extra post,
    2 ≤ available →
    iprop(⊢ sourceInput capacity fixed gen era cpu tier ξ original available extra -∗
      finish capacity image fixed whole gen era cpu tier ξ original available extra post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post)
end Xv6.Kernel.MycpuKptSource
