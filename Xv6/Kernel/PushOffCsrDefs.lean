import Xv6.Kernel.PushOffCodeDefs
import Xv6.Kernel.MycpuRegimeShellDefs
import MachCSL.Logic.SupervisorSstatusOffDefs

/-! Actual sstatus CSRRCI at push_off+0x0a, in the already-disabled source
regime. The physical mstatus write still occurs, although legalization
preserves its value under the source facts. Fetch/decode/cycles are separate. -/
namespace Xv6.Kernel.PushOffCsr
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev Shares := MycpuRegimeShell.Shares
abbrev Regime := MycpuRegimeShell.Regime
abbrev File := HartTp.GprFile
abbrev entry := MycpuRegimeShell.entry
noncomputable abbrev packet := @MycpuRegimeShell.resources

def index : PushOffCode.Index := ⟨5, by decide⟩
def body [Platform] : SailM ExecutionResult := execute (PushOffCode.normalized index)

def Config (rs : RegisterFile) : Prop :=
  rs .cur_privilege = .Supervisor ∧ rs .misa = SupervisorSstatusOff.misaValue

def afterValues (control : RegisterFile) (values : File) : File :=
  HartTp.set values 15#5 (lower_mstatus (control .mstatus))

def after (rs : RegisterFile) : RegisterFile :=
  MachCSL.Sail.Registers.write rs .x15 (lower_mstatus (rs .mstatus))

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

noncomputable def resources (era : Era.Record) (cpu : CPU) (regime : Regime)
    (control : RegisterFile) (values : File) (shares : Shares) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu regime control (afterValues control values) shares ∗ frame)

end Xv6.Kernel.PushOffCsr
