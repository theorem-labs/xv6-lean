import MachCSL.Logic.SupervisorRead4Defs
import MachCSL.Logic.SupervisorWrite4Defs
import MachCSL.Logic.SupervisorMemOuterDefs
import MachCSL.Machine.SupervisorBareDefs

namespace MachCSL.Logic.SupervisorMemOuter4
open Iris MachCSL.Machine LeanPaperStock.Functions
abbrev Shares := SupervisorMemOuter.Shares
abbrev footprint := SupervisorMemOuter.footprint
abbrev cells := @SupervisorMemOuter.cells
abbrev effective := SupervisorMemOuter.effective

abbrev ReadResult := _root_.Sail.Result (BitVec 32) (physaddr × ExceptionType)
def readProgram (address : BitVec 64) : SailM ReadResult :=
  mem_read (.Load .Data) .PBMT_PMA (.Physaddr address) 4 false false false

def writeProgram (address : BitVec 64) (word : BitVec 32) : SailM SupervisorWrite4.Result :=
  mem_write_value (.Physaddr address) 4 word (.Store .Data) .PBMT_PMA false false false

end MachCSL.Logic.SupervisorMemOuter4
