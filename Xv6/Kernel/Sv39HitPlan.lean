import Xv6.Kernel.Sv39HitFactor
import MachCSL.Logic.RegisterPlanProofs

namespace Xv6.Kernel.Sv39Hit
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem head_plan environment rs cached access :
    RegisterPlan.Returns (footprint environment) rs (head cached access) (headValue rs cached access) rs := by
  unfold head headValue
  cases eq : update_PTE_Bits cached access with
  | none => exact .pure ⟨rfl, rfl⟩
  | some word =>
    rw [SupervisorPteAD.gate_eq]
    exact .read (dq := environment) (by simp [footprint]) (.pure ⟨rfl, rfl⟩)

theorem resume_plan environment rs vpn idx ent response (_bound : idx < 64)
    (pbmt : PtTree.PbmtZero ent.pte) :
    RegisterPlan.Returns (footprint environment) rs (afterUpdate vpn idx ent response)
      (updateValue vpn ent response) (updateAfter rs idx ent response) := by
  have pbmt_eq : tlb_get_pbmt ent = pure page_based_mem_type.PBMT_PMA := by
    unfold tlb_get_pbmt
    dsimp only
    change _get_PTE_Ext_PBMT (ext_bits_of_PTE ent.pte) = 0#2 at pbmt
    rw [pbmt]
    rfl
  cases response with
  | Err error => exact .pure ⟨rfl, rfl⟩
  | Ok pair =>
    rcases pair with ⟨word, ext⟩
    cases word with
    | none =>
      simp only [afterUpdate, pbmt_eq, BootPmp.sail_pure_bind]
      exact .pure ⟨rfl, rfl⟩
    | some word =>
      simp only [afterUpdate, pbmt_eq, BootPmp.sail_pure_bind]
      unfold write_TLB
      rw [BootPmp.sail_bind_assoc]
      apply RegisterPlan.Plan.read (dq := .own 1) (by simp [footprint])
      apply RegisterPlan.Plan.write (by simp [footprint])
      exact .pure ⟨rfl, rfl⟩

theorem footprint_unique environment : RegisterFootprint.Unique (footprint environment) := by
  simp [RegisterFootprint.Unique, footprint]

end Xv6.Kernel.Sv39Hit
