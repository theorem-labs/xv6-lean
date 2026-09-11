import MachCSL.Machine.State
import MachCSL.Sail.Registers

/-! The thirteen-register predicate of paper `iris/CalleeSaved.v:34–48`.
TP is not callee-saved: a suspended thread may resume on another hart. -/
namespace Xv6.Kernel.CalleeSaved
open MachCSL.Machine

def registers : List Register :=
  [.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

def Preserved (before after : RegisterFile) : Prop :=
  ∀ r ∈ registers, after r = before r

/-- Typed writes, outermost first as in the source `apply_writes`.
Generalizing to all Sail registers also permits framing control updates. -/
abbrev Write := (r : Register) × RegisterType r

def applyWrites (writes : List Write) (rs : RegisterFile) : RegisterFile :=
  writes.foldr (fun rv rest => MachCSL.Sail.Registers.write rest rv.1 rv.2) rs

def outerWrite (r : Register) : List Write → Option (RegisterType r)
  | [] => none
  | ⟨k, v⟩ :: rest => if h : k = r then some (h ▸ v) else outerWrite r rest

def Restores (rs : RegisterFile) (writes : List Write) : Prop :=
  ∀ r ∈ registers, ∀ value, outerWrite r writes = some value → value = rs r

end Xv6.Kernel.CalleeSaved
