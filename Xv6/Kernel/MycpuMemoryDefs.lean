import Xv6.Kernel.MycpuDecodeProofs
import MachCSL.Logic.SupervisorAddressDefs
import MachCSL.Logic.SupervisorBareReadDefs
import MachCSL.Logic.SupervisorBareWriteDefs

namespace Xv6.Kernel.MycpuMemory
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

inductive Slot where | ra | s0
  deriving DecidableEq

def dataRegister : Slot → Register | .ra => .x1 | .s0 => .x8
def dataIndex : Slot → regidx | .ra => .Regidx 1#5 | .s0 => .Regidx 8#5
def offset : Slot → BitVec 64 | .ra => 8#64 | .s0 => 0#64
def immediate : Slot → BitVec 12 | .ra => 8#12 | .s0 => 0#12
def storeIndex : Slot → Fin 14 | .ra => ⟨1, by decide⟩ | .s0 => ⟨2, by decide⟩
def loadIndex : Slot → Fin 14 | .ra => ⟨10, by decide⟩ | .s0 => ⟨11, by decide⟩
def dataValue (slot : Slot) (rs : RegisterFile) : BitVec 64 :=
  match slot with | .ra => rs .x1 | .s0 => rs .x8
def after (slot : Slot) (rs : RegisterFile) (word : BitVec 64) : RegisterFile :=
  match slot with
  | .ra => MachCSL.Sail.Registers.write rs .x1 word
  | .s0 => MachCSL.Sail.Registers.write rs .x8 word
def address (slot : Slot) (rs : RegisterFile) : BitVec 64 := rs .x2 + offset slot

structure Shares where
  bare : SupervisorBareFetch.Shares
  envcfg : DFrac
  sp : DFrac
  data : DFrac

def footprint (slot : Slot) (shares : Shares) (dataShare : DFrac) : RegisterFootprint.Footprint :=
  [(.menvcfg, shares.envcfg), (.x2, shares.sp), (dataRegister slot, dataShare)] ++
    SupervisorBareFetch.footprint shares.bare

def addressShares (shares : Shares) : SupervisorAddress.Shares :=
  ⟨shares.bare.translation.status, shares.bare.translation.privilege,
    shares.envcfg, shares.bare.translation.satp⟩

structure ReadConfig (slot : Slot) (rs : RegisterFile) (region : PMA_Region) : Prop where
  transform : SupervisorAddress.Config rs .Bare
  memory : SupervisorBareRead.Config rs (address slot rs) region
structure WriteConfig (slot : Slot) (rs : RegisterFile) (region : PMA_Region) : Prop where
  transform : SupervisorAddress.Config rs .Bare
  memory : SupervisorBareWrite.Config rs (address slot rs) region

abbrev cells {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (slot : Slot) (shares : Shares)
    (dataShare : DFrac) : IProp GF :=
  RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint slot shares dataShare)

def storeBody [Platform] (slot : Slot) : SailM ExecutionResult := do
  match ← execute (MycpuDecode.decoded (storeIndex slot)) with
  | .ExecuteAs other => execute other
  | result => pure result

def loadBody [Platform] (slot : Slot) : SailM ExecutionResult := do
  match ← execute (MycpuDecode.decoded (loadIndex slot)) with
  | .ExecuteAs other => execute other
  | result => pure result

/-- Exact LOAD success suffix; the destination is one of the two nonzero registers. -/
def loadTail (slot : Slot) (word : BitVec 64) : SailM ExecutionResult := do
  wX_bits (dataIndex slot) word
  pure (.Retire_Success ())

end Xv6.Kernel.MycpuMemory
