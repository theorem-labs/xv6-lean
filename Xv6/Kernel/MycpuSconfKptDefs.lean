import Xv6.Kernel.MycpuKptDefs
import Xv6.Kernel.MycpuKptEntryDefs
import Xv6.Kernel.KernelTextImageDefs

/-! Source disabled mycpu capability contract for full tier. The boot-PMA
cell is an explicit retained specialization; all execution facts are derived
from the source input and internally linked native function theorem. -/
namespace Xv6.Kernel.MycpuSconfKpt
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev File := HartTp.GprFile
abbrev entryPC := MycpuKptEntry.entryPC

def returnPC (cpu : CPU) (original : File) : BitVec 64 :=
  MycpuReturn.retPC (HartTp.rget cpu original 1#5)

/-- The exact two source software conclusions: thirteen callee-saved keys
and a0 computed from the entry hart's pinned TP. -/
def Result (cpu : CPU) (original after : File) : Prop :=
  MycpuOff.Saved original after ∧ after 10#5 = MycpuScalar.mycpuRet (HartTp.rget cpu original 4#5)

variable {GF : BundledGFunctors} (capacity : Capacity GF)
variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def input (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (original : File) (available : Nat) (frame : IProp GF) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu .full ξ original available entryPC ∗
    KernelTextImage.text capacity.translation era .identity ∗ MycpuKptEntry.bootPma capacity era cpu ∗ frame)

noncomputable def restored (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (original after : File) (available : Nat) (frame : IProp GF) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu .full ξ after available (returnPC cpu original) ∗
    KernelTextImage.text capacity.translation era .identity ∗ MycpuKptEntry.bootPma capacity era cpu ∗ frame)

noncomputable def finish [Platform] (image : BootImage) (fixed : MachineInterp.FixedNames)
    (whole : List Observation) (gen : Nat) (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (original : File) (available : Nat) (frame : IProp GF) (post : Empty → IProp GF) : IProp GF :=
  iprop(∀ after, ⌜Result cpu original after⌝ -∗
    restored capacity fixed gen era cpu ξ original after available frame -∗
    ∀ nextTick, RegisterWP.threadWP capacity.machine image fixed whole (.hart gen cpu (cycle nextTick)) post)

end Xv6.Kernel.MycpuSconfKpt
