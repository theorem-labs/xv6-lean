import Xv6.Kernel.KptJalSourceDefs
import Xv6.Kernel.BareJalSourceDefs

/-! Unopened source disabled JAL-x1, preserving the original tier and
dispatching on the actual Bare/KPT slot. JAL uses no scratch stack words. -/
namespace Xv6.Kernel.JalSconf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev File := HartTp.GprFile
abbrev Tier := KernelDatum.Tier
abbrev afterFile := KptJal.afterValues
abbrev bootPma := @MycpuBareSource.bootPma

variable {GF : BundledGFunctors} (capacity : Capacity GF)
variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- The original source capability is unopened. Actual code ownership is
at the same tier; the retained boot-PMA cell is an explicit specialization. -/
noncomputable def input (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (tier : Tier) (ξ : TsoContext.CtxId) (file : File) (available : Nat)
    (pc : BitVec 64) (imm : BitVec 21) (extra : IProp GF) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu tier ξ file available pc ∗
    KptJal.code capacity era tier pc imm ∗ bootPma capacity era cpu ∗ extra)

/-- Exact same-tier source capability, unchanged scratch count, x1=PC+4
and source pc_is at target. Code/PMA/caller frame all return. -/
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

end Xv6.Kernel.JalSconf
