import Xv6.Kernel.SieOffCapabilityDefs
import Xv6.Kernel.MycpuScalarDefs
import MachCSL.Logic.LockSetDefs
import MachCSL.Logic.TsoContextBytesReadWPDefs
import LeanPaperStock.InterruptRegs

/-! Exact disabled `CpuOwn.cpu_own` resource. The static CPU fields retain
identity-tier virtual/context ownership. The active source count is only
an SIE eighth; no enabled arm, restore payload or boot execution is defined. -/
namespace Xv6.Kernel.CpuOwn
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure Capacity (GF : BundledGFunctors) where
  execution : MycpuRegimeShell.Capacity GF
  heldSets : LockSet.Capacity GF

abbrev Capacity.machine {GF : BundledGFunctors} (capacity : Capacity GF) := capacity.execution.machine
abbrev Held := LockSet.Names
abbrev Word := BitVec 64
abbrev SmallWord := BitVec 32

def cpuPointer (cpu : CPU) : Word := MycpuScalar.mycpuRet (HartTp.hartWord cpu)
def procAddress (cpu : CPU) : Word := cpuPointer cpu
def noffAddress (cpu : CPU) : Word := cpuPointer cpu + sign_extend (m := 64) 120#12
def intenaAddress (cpu : CPU) : Word := cpuPointer cpu + sign_extend (m := 64) 124#12

def noffValue (depth : Nat) : SmallWord := BitVec.ofNat 32 depth
def intenaValue (baseEnabled : Bool) : SmallWord := if baseEnabled then 1#32 else 0#32
/-- IntrDefs.MEDELEG_S: the actual legalizer, not an assumed CSR value. -/
def medelegS : Word := legalize_medeleg 0#64 0xffff#64

def Aligned4 (address : Word) : Prop := address.toNat % 4 = 0

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- TsoCtx.ctx_word4_pointsto at its source default KT0. Each byte keeps
its actual mapping claim and mirrored fractional timestamp/context resource. -/
def word4 (era : Era.Record) (ξ : TsoContext.CtxId) (address : Word)
    (dq : DFrac) (value : SmallWord) : IProp GF :=
  iprop(⌜Aligned4 address⌝ ∗ [∗list] j ∈ List.range 4,
    KernelDatum.byte capacity.execution.translation era .identity ξ (addressAdd address j) dq (nthByte value j))

def curProc (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId) (process : Word) : IProp GF :=
  KernelDatum.word capacity.execution.translation era .identity ξ (procAddress cpu) (.own 1) process

def count (era : Era.Record) (cpu : CPU) (depth : Nat) (baseEnabled : Bool) : IProp GF :=
  SupervisorBits.countBit capacity.execution.supervisorBits
    (SupervisorBits.namesOfEra era cpu) depth baseEnabled

abbrev off (era : Era.Record) (cpu : CPU) : IProp GF :=
  SieOffCapability.off capacity.execution era cpu

def cells (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (depth : Nat) (baseEnabled : Bool) (process : Word) : IProp GF :=
  iprop(⌜depth < 2^31⌝ ∗ word4 capacity era ξ (noffAddress cpu) (.own 1) (noffValue depth) ∗
    (match depth with
      | 0 => iprop(∃ value : SmallWord, word4 capacity era ξ (intenaAddress cpu) (.own 1) value)
      | _ + 1 => word4 capacity era ξ (intenaAddress cpu) (.own 1) (intenaValue baseEnabled)) ∗
    curProc capacity era cpu ξ process)

def hartCsrs (era : Era.Record) (cpu : CPU) : IProp GF :=
  iprop((∃ value : Word, Registers.regPointsto capacity.machine.era.registers
      (era.registers cpu) .sscratch (.own 1) value) ∗
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .medeleg .discard medelegS ∗
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .mstateen0 .discard 0#64 ∗
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .sstateen0 .discard 0#32)

def privateState (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (depth : Nat) (baseEnabled : Bool) (process : Word) (held : Held) : IProp GF :=
  iprop(cells capacity era cpu ξ depth baseEnabled process ∗
    LockSet.cpuLevel capacity.heldSets era cpu depth held ∗ hartCsrs capacity era cpu)

/-- Precisely the source b=false branch, independent of the executing tier.
No actual memory write or SIE flip follows merely from reindexing its token. -/
def ownOff (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (depth : Nat) (baseEnabled : Bool) (process : Word) (held : Held) : IProp GF :=
  iprop(privateState capacity era cpu ξ depth baseEnabled process held ∗
    count capacity era cpu depth baseEnabled)

end Xv6.Kernel.CpuOwn
