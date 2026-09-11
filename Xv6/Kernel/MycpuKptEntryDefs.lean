import Xv6.Kernel.SieOffPacketDefs
import Xv6.Kernel.MycpuKptCycleDefs

/-! Source disabled full-tier entry resources for mycpu's fixed save area.
This is a resource adapter, not an instruction or whole-function WP.
Literal boot PMA ownership is an explicit specialization of source hardware. -/
namespace Xv6.Kernel.MycpuKptEntry
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev File := HartTp.GprFile
abbrev Words := MycpuKptBody.Words
abbrev sp := SieOffCapability.sp

def entryPC : BitVec 64 := MycpuDecode.address ⟨0, by decide⟩

/-- The values initially occupying the save area are arbitrary source stack
contents, not the caller's saved RA/S0 values before the actual stores. -/
def words (first second : BitVec 64) : Words
  | .ra => first
  | .s0 => second

variable {GF : BundledGFunctors} (capacity : Capacity GF)

abbrev bootPma (era : Era.Record) (cpu : CPU) : IProp GF :=
  Registers.regPointsto capacity.machine.era.registers (era.registers cpu)
    .pma_regions .discard pmaBoot

/-- The exact untouched stack tail, anchored to the entry SP. -/
def tail (era : Era.Record) (ξ : TsoContext.CtxId) (entrySP : BitVec 64)
    (available : Nat) : IProp GF :=
  KernelStack.own capacity.translation era .full ξ (KernelStack.paStk entrySP 2) (available - 2)

variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- Original source capability and pc_is, plus two explicit persistent
specialization inputs. Code production from kernel_text is separate. -/
noncomputable def input (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (file : File) (available : Nat) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu .full ξ file available entryPC ∗
    bootPma capacity era cpu ∗ MycpuKptFetch.code capacity era .full)

/-- Every source remainder is explicit, including the linear shot and the
whole persistent hardware config. No running context is hidden here. -/
noncomputable def frame (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (entrySP : BitVec 64) (available : Nat) : IProp GF :=
  iprop(tail capacity era ξ entrySP available ∗ SieOffCapability.timer capacity era cpu ∗
    SieOffCapability.tierWitness capacity era cpu .full ∗ Sconf.hardware capacity fixed gen era cpu ∗
    SupervisorTranslation.shot capacity.translation era cpu ∗ bootPma capacity era cpu)

/-- The exact packet consumed by native KPT cycle/body rules. The fixed
save area is never reindexed when the current GPR file's SP changes. -/
noncomputable def resources (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (entrySP : BitVec 64) (available : Nat)
    (root : PtTree.PPN) (control : RegisterFile) (file : File) (saved : Words)
    (rr : Option Reservation) : IProp GF :=
  iprop(MycpuRegimeShell.resources capacity era cpu (.kpt KptGhost.kptN root) control file
      MycpuRegimeShell.sourceShares ∗ MycpuKptFetch.code capacity era .full ∗
    TsoContextReadWP.running capacity.machine era cpu ξ ∗
    MycpuKptBody.pair capacity era .full ξ entrySP saved ∗
    Reservations.resvFrag capacity.machine.era.reservations era.reservations cpu rr ∗
    frame capacity fixed gen era cpu ξ entrySP available)

/-- The restored source boundary, preserving the separately supplied text
and boot-PMA resources for its caller. -/
noncomputable def restored (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (ξ : TsoContext.CtxId) (file : File) (available : Nat) (returnPC : BitVec 64) : IProp GF :=
  iprop(SieOffPacket.input capacity fixed gen era cpu .full ξ file available returnPC ∗
    bootPma capacity era cpu ∗ MycpuKptFetch.code capacity era .full)

end Xv6.Kernel.MycpuKptEntry
