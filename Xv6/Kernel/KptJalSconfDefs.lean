import Xv6.Kernel.KptJalDefs
import Xv6.Kernel.MycpuKptEntryDefs

/-! Source disabled JAL-x1 capability rule in full translation tier.
The retained boot-PMA cell is explicit; JAL changes no stack resource. -/
namespace Xv6.Kernel.KptJalSconf
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev File := HartTp.GprFile
abbrev afterFile := KptJal.afterValues

variable {GF : BundledGFunctors} (capacity : Capacity GF)
variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def input (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (file : File) (available : Nat)
    (pc : BitVec 64) (imm : BitVec 21) (frame : IProp GF) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu .full ξ file available pc ∗
    KptJal.code capacity era .full pc imm ∗ MycpuKptEntry.bootPma capacity era cpu ∗ frame)

noncomputable def restored (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (file : File) (available : Nat)
    (pc : BitVec 64) (imm : BitVec 21) (frame : IProp GF) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu .full ξ (afterFile pc file) available (KptJal.target pc imm) ∗
    KptJal.code capacity era .full pc imm ∗ MycpuKptEntry.bootPma capacity era cpu ∗ frame)

noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (file : File) (available : Nat) (pc : BitVec 64) (imm : BitVec 21)
    (frame : IProp GF) (post : Empty → IProp GF) : IProp GF :=
  iprop(restored capacity fixed gen era cpu ξ file available pc imm frame -∗
    ∀ nextTick, RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post)

end Xv6.Kernel.KptJalSconf
