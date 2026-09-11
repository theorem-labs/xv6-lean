import MachCSL.Logic.SupervisorReadDefs
import MachCSL.Logic.SupervisorWriteDefs
import MachCSL.Machine.SupervisorBareDefs

namespace MachCSL.Logic.SupervisorMemOuter
open Iris MachCSL.Machine LeanPaperStock.Functions
structure Shares where
  status : DFrac
  privilege : DFrac

def footprint (shares : Shares) : RegisterFootprint.Footprint :=
  [(.mstatus, shares.status), (.cur_privilege, shares.privilege)]

abbrev cells {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.era.registers (era.registers cpu) rs (footprint shares)

def effective (access : MemoryAccessType mem_payload) : SailM Privilege := do
  effectivePrivilege access (← _root_.Sail.readReg .mstatus) (← _root_.Sail.readReg .cur_privilege)

abbrev ReadResult := _root_.Sail.Result (BitVec 64) (physaddr × ExceptionType)
def readProgram (kind : SupervisorRead.Kind) (address : BitVec 64) : SailM ReadResult :=
  mem_read (SupervisorRead.access kind) .PBMT_PMA (.Physaddr address) 8 false false false

def writeProgram (address word : BitVec 64) : SailM SupervisorWrite.Result :=
  mem_write_value (.Physaddr address) 8 word (.Store .Data) .PBMT_PMA false false false

end MachCSL.Logic.SupervisorMemOuter
