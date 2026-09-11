import Xv6.Kernel.MycpuRegimeShellDefs
import Xv6.Kernel.MycpuScalarDefs
import Xv6.Kernel.MycpuReturnDefs

/-! The ten register-only mycpu bodies on the source fifty-cell packet.
An arbitrary literal frame retains virtual save words at a fixed address
while the real SP updates change the software register map. -/
namespace Xv6.Kernel.MycpuKptRegister
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev Shares := MycpuRegimeShell.Shares
abbrev entry := MycpuRegimeShell.entry
noncomputable abbrev packet := @MycpuRegimeShell.resources

inductive Instruction where
  | scalar (index : Fin 9)
  | returns

def index : Instruction → Fin 14
  | .scalar i => MycpuScalar.index i
  | .returns => ⟨13, by decide⟩

/-- The actual generated execute/ExecuteAs body selection. -/
def body [Platform] (instruction : Instruction) : SailM ExecutionResult := do
  match ← execute (MycpuDecode.decoded (index instruction)) with
  | .ExecuteAs other => execute other
  | result => pure result

def scalarIndex (i : Fin 9) : HartTp.Index :=
  match i.val with
  | 0 => 2#5 | 1 => 8#5 | 2 | 3 | 4 => 15#5
  | 5 | 6 | 7 => 10#5 | _ => 2#5

/-- Explicit typed physical GPR correspondence, not register-constructor arithmetic. -/
def scalarRegister (i : Fin 9) : HartTp.TypedRegister :=
  match i.val with
  | 0 => ⟨.x2, rfl⟩ | 1 => ⟨.x8, rfl⟩ | 2 | 3 | 4 => ⟨.x15, rfl⟩
  | 5 | 6 | 7 => ⟨.x10, rfl⟩ | _ => ⟨.x2, rfl⟩

def scalarValue (i : Fin 9) (control : RegisterFile) (cpu : CPU) (values : HartTp.GprFile) : BitVec 64 :=
  cast (scalarRegister i).property (MycpuScalar.after i (entry control cpu values) (scalarRegister i).val)

def afterValues (instruction : Instruction) (control : RegisterFile) (cpu : CPU)
    (values : HartTp.GprFile) : HartTp.GprFile :=
  match instruction with
  | .scalar i => HartTp.set values (scalarIndex i) (scalarValue i control cpu values)
  | .returns => values

def afterControl (instruction : Instruction) (control : RegisterFile) (cpu : CPU)
    (values : HartTp.GprFile) : RegisterFile :=
  match instruction with
  | .scalar _ => control
  | .returns => MachCSL.Sail.Registers.write control .nextPC
      (MycpuReturn.retPC (HartTp.rget cpu values 1#5))

/-- Scalar bodies require no hardware-value premise. The return checks the
same actual Supervisor/LPE-disabled/C-enabled values as its native plan. -/
def Config : Instruction → RegisterFile → Prop
  | .scalar _, _ => True
  | .returns, control => MycpuReturn.Config control

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

noncomputable def resources (era : Era.Record) (cpu : CPU) (N : Namespace) (root : PtTree.PPN)
    (instruction : Instruction) (control : RegisterFile) (values : HartTp.GprFile)
    (shares : Shares) (frame : IProp GF) : IProp GF :=
  iprop(packet capacity era cpu (.kpt N root) (afterControl instruction control cpu values)
    (afterValues instruction control cpu values) shares ∗ frame)

end Xv6.Kernel.MycpuKptRegister
