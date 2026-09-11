import Xv6.Kernel.MycpuBareSourceDefs
import Xv6.Kernel.MycpuKptSourceDefs

/-! Tier-generic source disabled-mycpu contract. The actual source packet
selects its Bare or KPT branch; neither branch is assumed by the caller. -/
namespace Xv6.Kernel.MycpuSconf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev Tier := KernelDatum.Tier
abbrev File := HartTp.GprFile
abbrev entryPC := MycpuBareSource.entryPC
abbrev returnPC := MycpuBareSource.returnPC
abbrev Result := MycpuBareSource.Result
abbrev bootPma := @MycpuBareSource.bootPma

variable {GF : BundledGFunctors} (capacity : Capacity GF)
variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- Exact source capability and entry pc_is, identity kernel text, retained
same-hart boot-PMA specialization and a literal caller frame. -/
noncomputable def input (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (tier : Tier) (ξ : TsoContext.CtxId) (original : File) (available : Nat)
    (extra : IProp GF) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu tier ξ original available entryPC ∗
    KernelTextImage.text capacity.translation era .identity ∗ bootPma capacity era cpu ∗ extra)

/-- Restore the same source tier, context and stack count, with the actual
returned GPR file and PC at the low-bit-cleared original RA. -/
noncomputable def restored (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (tier : Tier) (ξ : TsoContext.CtxId) (original after : File) (available : Nat)
    (extra : IProp GF) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu tier ξ after available (returnPC cpu original) ∗
    KernelTextImage.text capacity.translation era .identity ∗ bootPma capacity era cpu ∗ extra)

noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (tier : Tier)
    (ξ : TsoContext.CtxId) (original : File) (available : Nat) (extra : IProp GF)
    (post : Empty → IProp GF) : IProp GF :=
  iprop(∀ after, ⌜Result cpu original after⌝ -∗
    restored capacity fixed gen era cpu tier ξ original after available extra -∗
    ∀ nextTick, RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post)

end Xv6.Kernel.MycpuSconf
