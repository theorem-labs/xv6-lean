import MachCSL.Logic.RegisterPlanDefs
import MachCSL.Machine.SupervisorPmpDefs

namespace MachCSL.Machine.SupervisorPhysical
open LeanPaperStock.Functions

/-- Bounded actual read families. The PTE path supports both reservation flags. -/
inductive SupportedRead : MemoryAccessType mem_payload → Nat → Bool → Prop
  | fetch2 : SupportedRead (.InstructionFetch ()) 2 false
  | fetch4 : SupportedRead (.InstructionFetch ()) 4 false
  | pte (reserved : Bool) : SupportedRead (.Load .PageTableEntry) 8 reserved
  | data : SupportedRead (.Load .Data) 8 false

/-- Only the attribute consumed by this actual read. Other attributes are arbitrary. -/
def ReadGrant (attributes : PMA) (access : MemoryAccessType mem_payload) : Prop :=
  match access with
  | .InstructionFetch () => attributes.executable = true
  | .Load .PageTableEntry => attributes.supports_pte_read = true
  | .Load .Data => attributes.readable = true
  | _ => False

def alignedInfo : Phys_Mem_Access_Info := ⟨.CannotSplit, 0⟩

/-- Positive bounded RAM interval; addition here is mathematical, not modular. -/
def RamRange (address : BitVec 64) (width : Nat) : Prop :=
  0 < width ∧ ramLow ≤ address.toNat ∧ address.toNat + width ≤ ramHigh

end MachCSL.Machine.SupervisorPhysical
