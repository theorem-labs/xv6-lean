import Xv6.Kernel.MycpuDecodeProofs
import MachCSL.Logic.RegisterPlanDefs

namespace Xv6.Kernel.MycpuScalar
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

/-- The nine non-memory, non-control instructions in the actual function. -/
def index (i : Fin 9) : Fin 14 :=
  match i.val with
  | 0 => ⟨0, by decide⟩ | 1 => ⟨3, by decide⟩ | 2 => ⟨4, by decide⟩
  | 3 => ⟨5, by decide⟩ | 4 => ⟨6, by decide⟩ | 5 => ⟨7, by decide⟩
  | 6 => ⟨8, by decide⟩ | 7 => ⟨9, by decide⟩ | _ => ⟨12, by decide⟩

/-- PC and actual x4/TP are independently fractional; written GPRs are full. -/
def footprint (pcShare tpShare : Iris.DFrac) : RegisterFootprint.Footprint :=
  [(.x2, .own 1), (.x8, .own 1), (.x15, .own 1), (.x10, .own 1),
   (.PC, pcShare), (.x4, tpShare)]

def after (i : Fin 9) (rs : RegisterFile) : RegisterFile :=
  match i.val with
  | 0 => MachCSL.Sail.Registers.write rs .x2 (rs .x2 + sign_extend (m := 64) 0xff0#12)
  | 1 => MachCSL.Sail.Registers.write rs .x8 (rs .x2 + sign_extend (m := 64) 16#12)
  | 2 => MachCSL.Sail.Registers.write rs .x15 (0#64 + rs .x4)
  | 3 => MachCSL.Sail.Registers.write rs .x15
      (sign_extend (m := 64) (_root_.Sail.BitVec.extractLsb (rs .x15 + sign_extend (m := 64) 0#12) 31 0))
  | 4 => MachCSL.Sail.Registers.write rs .x15 (_root_.Sail.shift_bits_left (rs .x15) 7#6)
  | 5 => MachCSL.Sail.Registers.write rs .x10 (rs .PC + sign_extend (m := 64) (17#20 +++ 0#12))
  | 6 => MachCSL.Sail.Registers.write rs .x10 (rs .x10 + sign_extend (m := 64) 0xb20#12)
  | 7 => MachCSL.Sail.Registers.write rs .x10 (rs .x10 + rs .x15)
  | _ => MachCSL.Sail.Registers.write rs .x2 (rs .x2 + sign_extend (m := 64) 16#12)

/-- Explicit register-event tree certified equal to the generated scalar body. -/
def program (i : Fin 9) : SailM ExecutionResult := do
  match i.val with
  | 0 => _root_.Sail.writeReg .x2 ((← _root_.Sail.readReg .x2) + sign_extend (m := 64) 0xff0#12)
  | 1 => _root_.Sail.writeReg .x8 ((← _root_.Sail.readReg .x2) + sign_extend (m := 64) 16#12)
  | 2 => _root_.Sail.writeReg .x15 (0#64 + (← _root_.Sail.readReg .x4))
  | 3 => _root_.Sail.writeReg .x15 (sign_extend (m := 64) (_root_.Sail.BitVec.extractLsb
      ((← _root_.Sail.readReg .x15) + sign_extend (m := 64) 0#12) 31 0))
  | 4 => _root_.Sail.writeReg .x15 (_root_.Sail.shift_bits_left (← _root_.Sail.readReg .x15) 7#6)
  | 5 => _root_.Sail.writeReg .x10 ((← _root_.Sail.readReg .PC) + sign_extend (m := 64) (17#20 +++ 0#12))
  | 6 => _root_.Sail.writeReg .x10 ((← _root_.Sail.readReg .x10) + sign_extend (m := 64) 0xb20#12)
  | 7 => _root_.Sail.writeReg .x10 ((← _root_.Sail.readReg .x10) + (← _root_.Sail.readReg .x15))
  | _ => _root_.Sail.writeReg .x2 ((← _root_.Sail.readReg .x2) + sign_extend (m := 64) 16#12)
  pure (.Retire_Success ())

/-- Actual run_hart_active execute/ExecuteAs selection, before retirement. -/
def body [Platform] (i : Fin 9) : SailM ExecutionResult := do
  match ← execute (MycpuDecode.decoded (index i)) with
  | .ExecuteAs other => execute other
  | result => pure result

/-- Source ProcGeom.mycpu_a5, retaining the exact modular machine operations. -/
def mycpuA5 (tp : BitVec 64) : BitVec 64 :=
  _root_.Sail.shift_bits_left
    (sign_extend (m := 64) (_root_.Sail.BitVec.extractLsb
      ((0#64 + tp) + sign_extend (m := 64) 0#12) 31 0)) 7#6

/-- Source ProcGeom.mycpu_ret: linked AUIPC/ADDI pair and modular hart offset. -/
def mycpuRet (tp : BitVec 64) : BitVec 64 :=
  ((MycpuDecode.address ⟨7, by decide⟩ + 0x11000#64) +
    sign_extend (m := 64) 0xb20#12) + mycpuA5 tp

def offsetCalc (rs : RegisterFile) : RegisterFile :=
  after ⟨4, by decide⟩ (after ⟨3, by decide⟩ (after ⟨2, by decide⟩ rs))
def addressCalc (rs : RegisterFile) : RegisterFile :=
  after ⟨7, by decide⟩ (after ⟨6, by decide⟩ (after ⟨5, by decide⟩ rs))

end Xv6.Kernel.MycpuScalar
