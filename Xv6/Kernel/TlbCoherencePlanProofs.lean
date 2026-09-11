import Xv6.Kernel.TlbCoherenceSpec
import Xv6.Kernel.Sv39TlbLink
import MachCSL.Logic.RegisterPlanProofs

namespace Xv6.Kernel.TlbCoherence
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem lookup_plan rs asid vpn : RegisterPlan.Returns Sv39Tlb.footprint rs
    (lookup_TLB 39 asid vpn) (lookupValue (rs .tlb) asid vpn) rs := by
  unfold lookup_TLB
  apply RegisterPlan.Plan.read (dq := .own 1) (by simp [Sv39Tlb.footprint])
  change RegisterPlan.Returns Sv39Tlb.footprint rs
    (match (rs .tlb)[index vpn]! with
      | none => pure none
      | some found => if match_TLB_Entry found asid (vpn.signExtend 45) then
          pure (some (index vpn, found)) else pure none) _ _
  unfold lookupValue
  cases selected : (rs .tlb)[index vpn]! with
  | none => exact RegisterPlan.Plan.pure ⟨rfl,rfl⟩
  | some ent =>
    by_cases matched : match_TLB_Entry ent asid (vpn.signExtend 45) = true
    · simp only [matched, if_true]
      exact RegisterPlan.Plan.pure ⟨rfl,rfl⟩
    · simp only [matched]
      exact RegisterPlan.Plan.pure ⟨rfl,rfl⟩

theorem fill_plan rs asid vpn p2 p1 word : RegisterPlan.Returns Sv39Tlb.footprint rs
    (add_to_TLB 39 asid vpn (PtTree.nextBase word) word (.Physaddr (PtTree.addr0 p1 vpn))
      0 (PtTree.globalAfter false p2 p1 word)) () (fillAfter rs asid vpn p2 p1 word) :=
  Sv39Tlb.fill_plan rs asid vpn (PtTree.nextBase word) word (.Physaddr (PtTree.addr0 p1 vpn))
    (PtTree.globalAfter false p2 p1 word)

theorem refresh_plan rs idx ent word (_bound : idx < 64) : RegisterPlan.Returns Sv39Tlb.footprint rs
    (write_TLB idx (tlb_set_pte (k_n := 8) ent word)) () (refreshAfter rs idx ent word) := by
  unfold write_TLB
  apply RegisterPlan.Plan.read (dq := .own 1) (by simp [Sv39Tlb.footprint])
  apply RegisterPlan.Plan.write (by simp [Sv39Tlb.footprint])
  exact RegisterPlan.Plan.pure ⟨rfl,rfl⟩

theorem pbmt_plan rs asid vpn p2 p1 word (pbmt : PtTree.PbmtZero word) :
    RegisterPlan.Returns [] rs (tlb_get_pbmt (entry asid vpn p2 p1 word)) .PBMT_PMA rs := by
  unfold tlb_get_pbmt
  change _get_PTE_Ext_PBMT (ext_bits_of_PTE word) = 0#2 at pbmt
  change RegisterPlan.Returns [] rs
    (page_based_mem_type_forwards (_get_PTE_Ext_PBMT (ext_bits_of_PTE word))) .PBMT_PMA rs
  rw [pbmt]
  exact RegisterPlan.Plan.pure ⟨rfl,rfl⟩

end Xv6.Kernel.TlbCoherence
