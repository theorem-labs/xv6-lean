import MachCSL.Logic.SupervisorDataPmaDefs

namespace MachCSL.Logic.SupervisorDataPma
open Iris MachCSL.Machine LeanPaperStock.Functions

/-- Exact finite plans, including the owned PMA read. No data value or
successful memory event is assumed or produced. -/
structure Spec : Prop where
  check : ∀ fp rs dq, (.pma_regions, dq) ∈ fp → ∀ kind address n region,
    matching_pma_region (rs .pma_regions) (.Physaddr address) n = some region →
    Grant kind (override_PMA region.attributes .PBMT_PMA) →
    is_aligned_paddr (.Physaddr address) n = true →
    RegisterPlan.Returns fp rs (program kind address n) (.Ok SupervisorPhysical.alignedInfo) rs
  priority : ∀ fp rs dq, (.pma_regions, dq) ∈ fp → ∀ kind address n region,
    matching_pma_region (rs .pma_regions) (.Physaddr address) n = some region →
    Grant kind (override_PMA region.attributes .PBMT_PMA) →
    is_aligned_paddr (.Physaddr address) n = true →
    RegisterPlan.Returns fp rs (SupervisorDataPma.priority kind address n)
      (.Ok SupervisorPhysical.alignedInfo) rs

end MachCSL.Logic.SupervisorDataPma
