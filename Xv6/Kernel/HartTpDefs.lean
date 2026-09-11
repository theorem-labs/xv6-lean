import MachCSL.Logic.EraDefs
import LeanPaperStock.Regs

/-! Source HartTp.v and WpGpr.v:98–136. A total 32-entry software map
backs exactly 31 actual typed register cells; x0 is a zero-value fact.
No CPU migration or function WP is provided by these definitions. -/
namespace Xv6.Kernel.HartTp
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

abbrev Index := BitVec 5
abbrev Word := BitVec 64
abbrev GprFile := Index → Word
abbrev TypedRegister := { r : Register // RegisterType r = Word }

def tp : Index := 4#5

def hartWord (cpu : CPU) : Word := BitVec.ofNat 64 cpu.val

def set (file : GprFile) (index : Index) (value : Word) : GprFile :=
  fun other => if other = index then value else file other

def pin (cpu : CPU) (file : GprFile) : GprFile := set file tp (hartWord cpu)
def rget (cpu : CPU) (file : GprFile) (index : Index) : Word := pin cpu file index

/-- Explicit source correspondence: constructor numbers are never used to
compute the physical GPR. The final arm is x31 because Index is five bits. -/
def physical (index : Index) : Option TypedRegister :=
  match index.toNat with
  | 0 => none
  | 1 => some ⟨.x1, rfl⟩
  | 2 => some ⟨.x2, rfl⟩
  | 3 => some ⟨.x3, rfl⟩
  | 4 => some ⟨.x4, rfl⟩
  | 5 => some ⟨.x5, rfl⟩
  | 6 => some ⟨.x6, rfl⟩
  | 7 => some ⟨.x7, rfl⟩
  | 8 => some ⟨.x8, rfl⟩
  | 9 => some ⟨.x9, rfl⟩
  | 10 => some ⟨.x10, rfl⟩
  | 11 => some ⟨.x11, rfl⟩
  | 12 => some ⟨.x12, rfl⟩
  | 13 => some ⟨.x13, rfl⟩
  | 14 => some ⟨.x14, rfl⟩
  | 15 => some ⟨.x15, rfl⟩
  | 16 => some ⟨.x16, rfl⟩
  | 17 => some ⟨.x17, rfl⟩
  | 18 => some ⟨.x18, rfl⟩
  | 19 => some ⟨.x19, rfl⟩
  | 20 => some ⟨.x20, rfl⟩
  | 21 => some ⟨.x21, rfl⟩
  | 22 => some ⟨.x22, rfl⟩
  | 23 => some ⟨.x23, rfl⟩
  | 24 => some ⟨.x24, rfl⟩
  | 25 => some ⟨.x25, rfl⟩
  | 26 => some ⟨.x26, rfl⟩
  | 27 => some ⟨.x27, rfl⟩
  | 28 => some ⟨.x28, rfl⟩
  | 29 => some ⟨.x29, rfl⟩
  | 30 => some ⟨.x30, rfl⟩
  | _ => some ⟨.x31, rfl⟩

def indices : List Index := (List.finRange 32).map BitVec.ofFin

def physicalKeys : List Register := indices.filterMap (fun i => (physical i).map Subtype.val)

/-- Actual one-read form, to be proved equal to generated rX_bits. -/
def readAt (index : Index) : SailM Word :=
  match physical index with
  | none => pure 0#64
  | some ⟨r, typed⟩ => do
      let value ← _root_.Sail.readReg r
      pure (typed ▸ value)

/-- View of the physical file uses hardwired x0, not a nonexistent cell. -/
def ofRegisters (registers : RegisterFile) : GprFile := fun index =>
  match physical index with
  | none => 0#64
  | some ⟨r, typed⟩ => typed ▸ registers r

variable {GF : BundledGFunctors} (capacity : Registers.Capacity GF)

/-- Source gpr_pt, with explicit arbitrary fraction for future read access. -/
def pointsto (registerName : GName) (index : Index) (dq : DFrac) (value : Word) : IProp GF :=
  match physical index with
  | none => iprop(⌜value = 0#64⌝)
  | some ⟨r, typed⟩ => Registers.regPointsto capacity registerName r dq (typed.symm ▸ value)

/-- Full source GPR ownership: all 32 keys, with a purely logical x0 slot. -/
def file (registerName : GName) (values : GprFile) : IProp GF :=
  iprop([∗list] index ∈ indices, pointsto capacity registerName index (.own 1) (values index))

/-- Exact untouched remainder, not an arbitrary restoration capability. -/
def remainder (registerName : GName) (values : GprFile) (selected : Index) : IProp GF :=
  iprop([∗list] index ∈ indices.filter (fun i => i != selected),
    pointsto capacity registerName index (.own 1) (values index))

def pinnedFile (era : Era.Record) (cpu : CPU) (values : GprFile) : IProp GF :=
  file capacity (era.registers cpu) (pin cpu values)

end Xv6.Kernel.HartTp
