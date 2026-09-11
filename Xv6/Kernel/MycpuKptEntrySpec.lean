import Xv6.Kernel.MycpuKptEntryDefs

namespace Xv6.Kernel.MycpuKptEntry
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

structure PureSpec : Prop where
  config : ∀ pc control, SieOffPacket.Ambient pc control →
    control .pma_regions = pmaBoot → MycpuKptCycle.Config control
  slot_ra : ∀ entrySP, MycpuKptBody.slotAddress entrySP .ra = KernelStack.paStk entrySP 1
  slot_s0 : ∀ entrySP, MycpuKptBody.slotAddress entrySP .s0 = KernelStack.paStk entrySP 2
  full_regime : ∀ regime : SieOffPacket.Regime,
    MycpuRegimeShell.Admits regime.shell .full → ∃ root, regime = .kpt root

/-- Opening and restoration are backed by actual resources. No per-step
Config, known save values, translated address, execution result or WP is input. -/
structure Spec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  save_area : ∀ era ξ entrySP available, 2 ≤ available →
    iprop(KernelStack.own capacity.translation era .full ξ entrySP available ⊣⊢
      ∃ saved : Words, MycpuKptBody.pair capacity era .full ξ entrySP saved ∗
        tail capacity era ξ entrySP available)
  open_entry : ∀ fixed gen era cpu ξ file available, 2 ≤ available →
    iprop(input capacity fixed gen era cpu ξ file available ⊢ ∃ root control saved rr,
      ⌜MycpuKptCycle.Config control⌝ ∗ ⌜SieOffPacket.Boundary entryPC control⌝ ∗
      resources capacity fixed gen era cpu ξ (sp file) available root control file saved rr)
  close_entry : ∀ fixed gen era cpu ξ entrySP available root control file saved rr returnPC,
    2 ≤ available → sp file = entrySP → SieOffPacket.Boundary returnPC control →
    iprop(resources capacity fixed gen era cpu ξ entrySP available root control file saved rr ⊢
      restored capacity fixed gen era cpu ξ file available returnPC)
  certificate : ∀ fixed gen era cpu ξ entrySP available root control file saved rr,
    iprop(resources capacity fixed gen era cpu ξ entrySP available root control file saved rr ⊢
      MachineInterp.generationCertificate capacity.machine fixed gen era ∗
      resources capacity fixed gen era cpu ξ entrySP available root control file saved rr)

end Xv6.Kernel.MycpuKptEntry
