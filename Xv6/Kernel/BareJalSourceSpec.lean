import Xv6.Kernel.BareJalSourceDefs

namespace Xv6.Kernel.BareJalSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  config : ∀ pc control, SieOffPacket.Ambient pc control → control .pma_regions = pmaBoot →
    BareJal.Config control
  stack : ∀ pc file, SieOffCapability.sp (afterFile pc file) = SieOffCapability.sp file
  saved : ∀ pc file, MycpuOff.Saved file (afterFile pc file)
  boundary : ∀ pc imm control after, SieOffPacket.Boundary pc control →
    MycpuRegimeShell.Completed (KptJal.afterControl pc imm (KptJal.started control)) after →
    SieOffPacket.Boundary (KptJal.target pc imm) after

structure ResourceSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  open_entry : ∀ fixed gen era cpu ξ file available pc imm extra,
    iprop(input capacity fixed gen era cpu ξ file available pc imm extra ⊢ ∃ control rr,
      ⌜BareJal.Config control⌝ ∗ ⌜SieOffPacket.Ambient pc control⌝ ∗
      resources capacity fixed gen era cpu ξ file available control pc imm rr extra)
  close_entry : ∀ fixed gen era cpu ξ file available control codePC currentPC imm rr extra,
    SieOffPacket.Boundary currentPC control →
    iprop(resources capacity fixed gen era cpu ξ file available control codePC imm rr extra ⊢
      restored capacity fixed gen era cpu ξ file available codePC currentPC imm extra)
  kept_update : ∀ fixed gen era cpu ξ file available pc extra,
    iprop(kept capacity fixed gen era cpu ξ file available extra ⊣⊢
      kept capacity fixed gen era cpu ξ (afterFile pc file) available extra)
  certificate : ∀ fixed gen era cpu ξ file available control pc imm rr extra,
    iprop(resources capacity fixed gen era cpu ξ file available control pc imm rr extra ⊢
      MachineInterp.generationCertificate capacity.machine fixed gen era ∗
      resources capacity fixed gen era cpu ξ file available control pc imm rr extra)

/-- Actual opened-source Bare branch; no minimum free stack count and no
fetch/configuration/success WP supplied by the caller. Identity tier alone
does not select Bare, so the opened Bare lane remains explicit in input. -/
structure Spec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  cycle : ∀ image fixed whole gen era cpu ξ file available pc imm tick extra post,
    KptJal.TargetEven pc imm →
    iprop(⊢ input capacity fixed gen era cpu ξ file available pc imm extra -∗
      finish capacity image fixed whole gen era cpu ξ file available pc imm extra post -∗
      RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle tick)) post)

end Xv6.Kernel.BareJalSource
