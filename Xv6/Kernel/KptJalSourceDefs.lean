import Xv6.Kernel.KptJalDefs
import Xv6.Kernel.MycpuKptEntryDefs

/-! The actual opened KPT arm of source disabled JAL-x1, preserving either
original translation tier. JAL does not consume or reindex stack slots. -/
namespace Xv6.Kernel.KptJalSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev File := HartTp.GprFile
abbrev Tier := KernelDatum.Tier
abbrev afterFile := KptJal.afterValues
abbrev bootPma := @MycpuKptEntry.bootPma

variable {GF : BundledGFunctors} (capacity : Capacity GF)
variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- Literal opened KPT branch from the source packet. The caller does not
supply a register Config, known translation result or component WP. -/
noncomputable def input (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (tier : Tier) (ξ : TsoContext.CtxId) (file : File) (available : Nat)
    (pc : BitVec 64) (imm : BitVec 21) (extra : IProp GF) : IProp GF :=
  iprop((∃ root control, ⌜SieOffPacket.Ambient pc control⌝ ∗
      SieOffPacket.opened capacity fixed gen era cpu tier ξ file available (.kpt root) control) ∗
    KptJal.code capacity era tier pc imm ∗ bootPma capacity era cpu ∗ extra)

/-- Exact untouched source frame, with the original tier and full stack
depth. Running context and folded translation packet are handled separately. -/
noncomputable def sourceFrame (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (tier : Tier) (ξ : TsoContext.CtxId) (file : File) (available : Nat)
    (extra : IProp GF) : IProp GF :=
  iprop(KernelStack.own capacity.translation era tier ξ (SieOffCapability.sp file) available ∗
    SieOffCapability.timer capacity era cpu ∗ SieOffCapability.tierWitness capacity era cpu tier ∗
    Sconf.hardware capacity fixed gen era cpu ∗ SupervisorTranslation.shot capacity.translation era cpu ∗ extra)

/-- Only x1 changes: it receives the actual JAL link PC+4. Source capability
and all stack slots return at the target with the original tier intact. -/
noncomputable def restored (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (tier : Tier) (ξ : TsoContext.CtxId) (file : File) (available : Nat)
    (pc : BitVec 64) (imm : BitVec 21) (extra : IProp GF) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu tier ξ (afterFile pc file) available (KptJal.target pc imm) ∗
    KptJal.code capacity era tier pc imm ∗ bootPma capacity era cpu ∗ extra)

noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (tier : Tier)
    (ξ : TsoContext.CtxId) (file : File) (available : Nat) (pc : BitVec 64) (imm : BitVec 21)
    (extra : IProp GF) (post : Empty → IProp GF) : IProp GF :=
  iprop(restored capacity fixed gen era cpu tier ξ file available pc imm extra -∗
    ∀ nextTick, RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post)

end Xv6.Kernel.KptJalSource
