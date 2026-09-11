import Xv6.Kernel.KptJalSourceDefs
import Xv6.Kernel.MycpuSconfDefs

/-! Source JAL-to-mycpu caller from an actual opened KPT arm, preserving
either original translation tier through both native execution rules. -/
namespace Xv6.Kernel.MycpuCallKptSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev File := HartTp.GprFile
abbrev Tier := KernelDatum.Tier
abbrev Result := MycpuSconf.Result
abbrev bootPma := @MycpuSconf.bootPma

variable {GF : BundledGFunctors} (capacity : Capacity GF)
variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- Literal opened KPT source arm. Identity tier does not itself determine
the regime; the native slot resources supply this branch and its root. -/
noncomputable def input (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (tier : Tier) (ξ : TsoContext.CtxId) (original : File) (available : Nat)
    (pc : BitVec 64) (imm : BitVec 21) (extra : IProp GF) : IProp GF :=
  iprop((∃ root control, ⌜SieOffPacket.Ambient pc control⌝ ∗
      SieOffPacket.opened capacity fixed gen era cpu tier ξ original available (.kpt root) control) ∗
    KptJal.code capacity era tier pc imm ∗ KernelTextImage.text capacity.translation era .identity ∗
    bootPma capacity era cpu ∗ extra)

/-- Exact unopened source capability, with its original tier and stack
depth, at the actual JAL link PC+4. All code/text/PMA/frame inputs return. -/
noncomputable def restored (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (tier : Tier) (ξ : TsoContext.CtxId) (after : File) (available : Nat)
    (pc : BitVec 64) (imm : BitVec 21) (extra : IProp GF) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu tier ξ after available (KptJal.link pc) ∗
    KptJal.code capacity era tier pc imm ∗ KernelTextImage.text capacity.translation era .identity ∗
    bootPma capacity era cpu ∗ extra)

noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (tier : Tier)
    (ξ : TsoContext.CtxId) (original : File) (available : Nat) (pc : BitVec 64) (imm : BitVec 21)
    (extra : IProp GF) (post : Empty → IProp GF) : IProp GF :=
  iprop(∀ after, ⌜Result cpu original after⌝ -∗
    restored capacity fixed gen era cpu tier ξ after available pc imm extra -∗
    ∀ nextTick, RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post)

end Xv6.Kernel.MycpuCallKptSource
