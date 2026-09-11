import MachCSL.Logic.SupervisorFetchReadDefs

/-! Four-byte ordinary physical reads. Only the generic plain-event
boundary is shared with instruction fetch; the actual access is Load.Data. -/
namespace MachCSL.Logic.SupervisorRead4
open Iris MachCSL.Machine LeanPaperStock.Functions
abbrev Shares := SupervisorFetchRead.Shares
abbrev footprint := SupervisorFetchRead.footprint
abbrev cells := @SupervisorFetchRead.cells
abbrev Result := SupervisorFetchRead.Result 4

def program (address : BitVec 64) : SailM Result :=
  checked_mem_read (.Load .Data) .PBMT_PMA .Supervisor (.Physaddr address) 4
    false false false false

end MachCSL.Logic.SupervisorRead4
