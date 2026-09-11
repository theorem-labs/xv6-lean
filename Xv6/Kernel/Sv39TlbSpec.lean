import Xv6.Kernel.Sv39TlbDefs

namespace Xv6.Kernel.Sv39Tlb
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

structure Spec : Prop where
  index_bound : ∀ vpn, index vpn < 64
  selected : ∀ old asid vpn ppn pte address global,
    (filled old asid vpn ppn pte address global)[index vpn]? =
      some (some (entry asid vpn ppn pte address global))
  other : ∀ old asid vpn ppn pte address global i, i ≠ index vpn →
    (filled old asid vpn ppn pte address global)[i]? = old[i]?
  entry_matches : ∀ asid vpn ppn pte address global,
    match_TLB_Entry (entry asid vpn ppn pte address global) asid (vpn.signExtend 45) = true
  fill_plan : ∀ rs asid vpn ppn pte address global,
    RegisterPlan.Returns footprint rs
      (add_to_TLB 39 asid vpn ppn pte address 0 global) ()
      (after rs asid vpn ppn pte address global)
  lookup_plan : ∀ rs asid vpn ppn pte address global,
    RegisterPlan.Returns footprint (after rs asid vpn ppn pte address global)
      (lookup_TLB 39 asid vpn) (some (index vpn, entry asid vpn ppn pte address global))
      (after rs asid vpn ppn pte address global)

end Xv6.Kernel.Sv39Tlb
