import MachCSL.Machine.SupervisorPhysicalDefs

namespace MachCSL.Machine.SupervisorPhysical
open LeanPaperStock.Functions

theorem supported_width {access n reserved} (supported : SupportedRead access n reserved) :
    n = 2 ∨ n = 4 ∨ n = 8 := by cases supported <;> simp

theorem supported_positive {access n reserved} (supported : SupportedRead access n reserved) :
    0 < n := by cases supported <;> decide

theorem supported_pmp {access n reserved} (supported : SupportedRead access n reserved) :
    SupervisorPmp.Supported access := by
  cases supported
  · exact .fetch
  · exact .fetch
  · exact .pte
  · exact .load

theorem clint_ram (address : BitVec 64) (width : Nat) (range : RamRange address width) :
    within_clint (.Physaddr address) width = (pure false : SailM Bool) := by
  change (pure ((0x2000000 ≤b (address.toNat : Int)) &&
    (((address.toNat : Int) + (width : Int)) ≤b 0x20c0000)) : SailM Bool) = pure false
  have upper : ¬ ((address.toNat : Int) + (width : Int) ≤ 0x20c0000) := by
    rcases range with ⟨positive, low, fits⟩
    simp only [ramLow] at low
    omega
  simp [upper]

theorem sig_ram (address : BitVec 64) (width : Nat) :
    within_sig (.Physaddr address) width = (pure false : SailM Bool) := rfl

/-- The actual node-level device guard follows from the same RAM lower bound. -/
theorem device_ram (address : BitVec 64) (width : Nat) (range : RamRange address width) :
    deviceAddress address = false := by
  unfold deviceAddress
  simp only [RamRange, ramLow] at range
  simp [Nat.not_lt.mpr range.2.1]

end MachCSL.Machine.SupervisorPhysical
