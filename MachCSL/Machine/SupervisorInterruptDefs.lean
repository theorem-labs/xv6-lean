import MachCSL.Logic.EventWPDefs
import MachCSL.Machine.JalLoopReadOnly

/-! Supervisor interrupt suppression from the exact source delegation/SIE facts. -/
namespace MachCSL.Machine.SupervisorInterrupt
open LeanPaperStock.Functions

structure Disabled (rs : RegisterFile) : Prop where
  supervisorEnabled : _get_Misa_S (rs .misa) = 1#1
  delegated : rs .mie &&& ~~~(rs .mideleg) = 0#64
  sie : (_get_Mstatus_SIE (rs .mstatus) == 1#1) = false

/-- Actual generated platform-pending construction when S is enabled. -/
def externalValue (meip seip : BitVec 1) : BitVec 64 :=
  _update_Minterrupts_SEI (_update_Minterrupts_MEI (Mk_Minterrupts 0#64) meip) seip

def pendingValue (rs : RegisterFile) (meip seip : BitVec 1) : BitVec 64 :=
  Mk_Minterrupts (rs .mip ||| externalValue meip seip)

end MachCSL.Machine.SupervisorInterrupt
