import Xv6.Kernel.KptJalSconfDefs
import Xv6.Kernel.MycpuSconfKptDefs

namespace Xv6.Kernel.MycpuCallSconfKpt
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
abbrev Capacity := MycpuRegimeShell.Capacity
abbrev File := HartTp.GprFile
abbrev Result := MycpuSconfKpt.Result

variable {GF : BundledGFunctors} (capacity : Capacity GF)
variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def input (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (original : File) (available : Nat)
    (pc : BitVec 64) (imm : BitVec 21) (frame : IProp GF) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu .full ξ original available pc ∗
    KptJal.code capacity era .full pc imm ∗ KernelTextImage.text capacity.translation era .identity ∗
    MycpuKptEntry.bootPma capacity era cpu ∗ frame)

noncomputable def restored (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (after : File) (available : Nat)
    (pc : BitVec 64) (imm : BitVec 21) (frame : IProp GF) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu .full ξ after available (KptJal.link pc) ∗
    KptJal.code capacity era .full pc imm ∗ KernelTextImage.text capacity.translation era .identity ∗
    MycpuKptEntry.bootPma capacity era cpu ∗ frame)

noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (original : File) (available : Nat) (pc : BitVec 64) (imm : BitVec 21)
    (frame : IProp GF) (post : Empty → IProp GF) : IProp GF :=
  iprop(∀ after, ⌜Result cpu original after⌝ -∗
    restored capacity fixed gen era cpu ξ after available pc imm frame -∗
    ∀ nextTick, RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post)

end Xv6.Kernel.MycpuCallSconfKpt
