import Xv6.Kernel.Sv39TlbSpec
import MachCSL.Logic.RegisterPlanProofs

namespace Xv6.Kernel.Sv39Tlb
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem index_bound (vpn : BitVec 27) : index vpn < 64 := by
  change (vpn.extractLsb 5 0).toNat < 64
  exact (vpn.extractLsb 5 0).isLt

theorem selected old asid vpn ppn pte address global :
    (filled old asid vpn ppn pte address global)[index vpn]? =
      some (some (entry asid vpn ppn pte address global)) := by
  simp [filled, _root_.Sail.vectorUpdate, index_bound]

theorem other old asid vpn ppn pte address global i (different : i ≠ index vpn) :
    (filled old asid vpn ppn pte address global)[i]? = old[i]? := by
  simp [filled, _root_.Sail.vectorUpdate, Ne.symm different]

theorem entry_matches asid vpn ppn pte address global :
    match_TLB_Entry (entry asid vpn ppn pte address global) asid (vpn.signExtend 45) = true := by
  simp only [match_TLB_Entry, entry, beq_self_eq_true, Bool.or_true, Bool.true_and,
    BitVec.not_zero, BitVec.and_allOnes]

/-- The final callback read remains an actual universally quantified event. -/
theorem fill_plan (rs : RegisterFile) (asid : BitVec 16) (vpn : BitVec 27)
    (ppn : BitVec 44) (pte : BitVec 64) (address : physaddr) (global : Bool) :
    RegisterPlan.Returns footprint rs (add_to_TLB 39 asid vpn ppn pte address 0 global) ()
      (after rs asid vpn ppn pte address global) := by
  unfold add_to_TLB
  apply RegisterPlan.Plan.read (dq := .own 1) (by simp [footprint])
  apply RegisterPlan.Plan.write (by simp [footprint])
  apply RegisterPlan.Plan.readAny
  intro current
  apply RegisterPlan.Plan.pure
  constructor
  · rfl
  · unfold after filled entry
    congr 2
    change some (TLB_Entry.mk asid global ((vpn &&& ~~~0#27).signExtend 45)
      0#45 (ppn &&& ~~~0#44) pte address) = _
    simp only [BitVec.not_zero, BitVec.and_allOnes]

theorem lookup_plan rs asid vpn ppn pte address global :
    RegisterPlan.Returns footprint (after rs asid vpn ppn pte address global)
      (lookup_TLB 39 asid vpn) (some (index vpn, entry asid vpn ppn pte address global))
      (after rs asid vpn ppn pte address global) := by
  unfold lookup_TLB
  apply RegisterPlan.Plan.read (dq := .own 1) (by simp [footprint])
  have atIndex : (after rs asid vpn ppn pte address global .tlb)[index vpn]! =
      some (entry asid vpn ppn pte address global) := by
    simp only [after, MachCSL.Sail.Registers.write_same]
    change ((filled (rs .tlb) asid vpn ppn pte address global)[index vpn]?).getD default = _
    rw [selected]
    rfl
  change RegisterPlan.Returns footprint _
    (match (after rs asid vpn ppn pte address global .tlb)[index vpn]! with
      | none => pure none
      | some found => if match_TLB_Entry found asid (vpn.signExtend 45) then
          pure (some (index vpn, found)) else pure none) _ _
  rw [atIndex]
  dsimp only
  erw [entry_matches]
  exact .pure ⟨rfl, rfl⟩

theorem actual : Spec := ⟨index_bound, selected, other, entry_matches, fill_plan, lookup_plan⟩

end Xv6.Kernel.Sv39Tlb
