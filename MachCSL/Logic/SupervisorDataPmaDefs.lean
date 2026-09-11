import MachCSL.Machine.SupervisorPhysicalDefs

/-! Ordinary data PMA checks for a supplied byte width. Alignment and the
actual matching region discharge the generated permission path. -/
namespace MachCSL.Logic.SupervisorDataPma
open Iris MachCSL.Machine LeanPaperStock.Functions

inductive Kind where
  | load | store
  deriving DecidableEq

def access : Kind → MemoryAccessType mem_payload
  | .load => .Load .Data
  | .store => .Store .Data

def Grant : Kind → PMA → Prop
  | .load, attributes => attributes.readable = true
  | .store, attributes => attributes.writable = true

def program (kind : Kind) (address : BitVec 64) (n : Nat) :=
  pmaCheck (.Physaddr address) n (access kind) .PBMT_PMA false

def priority (kind : Kind) (address : BitVec 64) (n : Nat) :=
  check_pma_with_pmp_priority (access kind) .PBMT_PMA .Supervisor (.Physaddr address) n false

end MachCSL.Logic.SupervisorDataPma
