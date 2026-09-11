import MachCSL.Logic.TsoContextWordProofs
import MachCSL.Logic.TsoContextStoreLink
import LeanPaperStock.SplitAccessUtils

namespace MachCSL.Logic.TsoContextWord
open Iris MachCSL.Memory

abbrev registry := TsoContext.registry
abbrev registryCapacity := TsoContext.registryCapacity

theorem registrySpec : Spec registryCapacity := actual registryCapacity

theorem context_capacity_same : registryCapacity = TsoContext.registryCapacity := rfl

/-- Exact generated Sail alignment test, rather than an assumed stronger alignment. -/
theorem aligned_iff_sail (a : PhysicalAddress) :
    Aligned a ↔ LeanPaperStock.Functions.is_aligned_paddr (.Physaddr a) 8 = true := by
  change a.toNat % 8 = 0 ↔ ((Int.tmod (Int.ofNat a.toNat) (Int.ofNat 8)) == 0) = true
  change a.toNat % 8 = 0 ↔ ((Int.ofNat (a.toNat % 8)) == 0) = true
  rw [beq_iff_eq]
  exact ⟨fun h => congrArg Int.ofNat h, fun h => Int.ofNat.inj h⟩

end MachCSL.Logic.TsoContextWord
