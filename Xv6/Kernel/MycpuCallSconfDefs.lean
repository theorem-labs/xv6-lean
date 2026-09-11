import Xv6.Kernel.JalSconfDefs
import Xv6.Kernel.MycpuSconfDefs

/-! Source JAL-to-mycpu caller from the unopened disabled capability at
either original tier. Both actual translation-slot branches are supported. -/
namespace Xv6.Kernel.MycpuCallSconf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev File := HartTp.GprFile
abbrev Tier := KernelDatum.Tier
abbrev Result := MycpuSconf.Result
abbrev bootPma := @MycpuSconf.bootPma

variable {GF : BundledGFunctors} (capacity : Capacity GF)
variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- Exact source capability and instruction resources. No opened arm,
root, configuration, physical word or component WP is an input. -/
noncomputable def input (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (tier : Tier) (ξ : TsoContext.CtxId) (original : File) (available : Nat)
    (pc : BitVec 64) (imm : BitVec 21) (extra : IProp GF) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu tier ξ original available pc ∗
    KptJal.code capacity era tier pc imm ∗ KernelTextImage.text capacity.translation era .identity ∗
    bootPma capacity era cpu ∗ extra)

/-- Original-tier source capability at PC+4, retaining the entire scratch
count, code/text/PMA and caller frame after the actual function returns. -/
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

end Xv6.Kernel.MycpuCallSconf
