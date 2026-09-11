import Xv6.Kernel.PushOffCodeDefs
import Xv6.Kernel.MycpuRegimeShellDefs
import Xv6.Kernel.MycpuReturnDefs

/-! Register-only normalized push_off bodies. The actual decode/ExecuteAs
certificates, fetch, retirement and source-function resources are separate. -/
namespace Xv6.Kernel.PushOffScalar
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev Shares := MycpuRegimeShell.Shares
abbrev Regime := MycpuRegimeShell.Regime
abbrev File := HartTp.GprFile
abbrev entry := MycpuRegimeShell.entry
noncomputable abbrev packet := @MycpuRegimeShell.resources

inductive Instruction where
  | subSP | framePointer | saveStatus | branchZero | increment
  | restoreSP | returns | shift | mask | jumpBack
  deriving DecidableEq

def index : Instruction → PushOffCode.Index
  | .subSP => ⟨0, by decide⟩
  | .framePointer => ⟨4, by decide⟩
  | .saveStatus => ⟨6, by decide⟩
  | .branchZero => ⟨9, by decide⟩
  | .increment => ⟨12, by decide⟩
  | .restoreSP => ⟨17, by decide⟩
  | .returns => ⟨18, by decide⟩
  | .shift => ⟨20, by decide⟩
  | .mask => ⟨21, by decide⟩
  | .jumpBack => ⟨23, by decide⟩

/-- Exactly the normalized generated execute call, with no assumed expansion. -/
def body [Platform] (i : Instruction) : SailM ExecutionResult :=
  execute (PushOffCode.normalized (index i))

def destination : Instruction → Option HartTp.Index
  | .subSP | .restoreSP => some 2#5
  | .framePointer => some 8#5
  | .saveStatus => some 9#5
  | .increment | .shift | .mask => some 15#5
  | .branchZero | .returns | .jumpBack => none

def branchTaken (cpu : CPU) (values : File) : Bool := HartTp.rget cpu values 15#5 == 0#64

def afterValues (i : Instruction) (cpu : CPU) (values : File) : File :=
  match i with
  | .subSP => HartTp.set values 2#5 (HartTp.rget cpu values 2#5 + sign_extend (m := 64) 0xfe0#12)
  | .framePointer => HartTp.set values 8#5 (HartTp.rget cpu values 2#5 + 32#64)
  | .saveStatus => HartTp.set values 9#5 (0#64 + HartTp.rget cpu values 15#5)
  | .increment => HartTp.set values 15#5
      (sign_extend (m := 64) (Sail.BitVec.extractLsb (HartTp.rget cpu values 15#5 + 1#64) 31 0))
  | .restoreSP => HartTp.set values 2#5 (HartTp.rget cpu values 2#5 + 32#64)
  | .shift => HartTp.set values 15#5 (_root_.Sail.shift_bits_right (HartTp.rget cpu values 9#5) 1#6)
  | .mask => HartTp.set values 15#5 (HartTp.rget cpu values 15#5 &&& 1#64)
  | .branchZero | .returns | .jumpBack => values

/-- Untaken BEQ leaves the already-prepared nextPC untouched. The JR and
C.J link destinations are x0, so their eager nextPC reads cause no GPR write. -/
def afterControl (i : Instruction) (control : RegisterFile) (cpu : CPU) (values : File) : RegisterFile :=
  match i with
  | .branchZero => if branchTaken cpu values then
      MachCSL.Sail.Registers.write control .nextPC (control .PC + 22#64) else control
  | .returns => MachCSL.Sail.Registers.write control .nextPC (MycpuReturn.retPC (HartTp.rget cpu values 1#5))
  | .jumpBack => MachCSL.Sail.Registers.write control .nextPC (control .PC + sign_extend (m := 64) 0x1fffe0#21)
  | _ => control

/-- Physical post-file for the actual register-only execution certificate. -/
def after (i : Instruction) (rs : RegisterFile) : RegisterFile :=
  match i with
  | .subSP => MachCSL.Sail.Registers.write rs .x2 (rs .x2 + sign_extend (m := 64) 0xfe0#12)
  | .framePointer => MachCSL.Sail.Registers.write rs .x8 (rs .x2 + 32#64)
  | .saveStatus => MachCSL.Sail.Registers.write rs .x9 (0#64 + rs .x15)
  | .branchZero => if rs .x15 == 0#64 then MachCSL.Sail.Registers.write rs .nextPC (rs .PC + 22#64) else rs
  | .increment => MachCSL.Sail.Registers.write rs .x15
      (sign_extend (m := 64) (Sail.BitVec.extractLsb (rs .x15 + 1#64) 31 0))
  | .restoreSP => MachCSL.Sail.Registers.write rs .x2 (rs .x2 + 32#64)
  | .returns => MachCSL.Sail.Registers.write rs .nextPC (MycpuReturn.retPC (rs .x1))
  | .shift => MachCSL.Sail.Registers.write rs .x15 (_root_.Sail.shift_bits_right (rs .x9) 1#6)
  | .mask => MachCSL.Sail.Registers.write rs .x15 (rs .x15 &&& 1#64)
  | .jumpBack => MachCSL.Sail.Registers.write rs .nextPC (rs .PC + sign_extend (m := 64) 0x1fffe0#21)

/-- Values needed only by the actual control-flow paths. MISA.C=1 still
requires the generated eager read; source instruction addresses prove even PC.
No arithmetic instruction requires a hardware-value premise. -/
def Config : Instruction → RegisterFile → Prop
  | .branchZero, rs | .jumpBack, rs =>
      _get_Misa_C (rs .misa) = 1#1 ∧ Sail.BitVec.access (rs .PC) 0 = 0#1
  | .returns, rs => MycpuReturn.Config rs
  | _, _ => True

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

/-- Translation resources are framed at the exact same actual regime.
The literal frame can retain anchored stack words, running context and rr. -/
noncomputable def resources (era : Era.Record) (cpu : CPU) (regime : Regime)
    (i : Instruction) (control : RegisterFile) (values : File) (shares : Shares)
    (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu regime (afterControl i control cpu values)
    (afterValues i cpu values) shares ∗ frame)

end Xv6.Kernel.PushOffScalar
