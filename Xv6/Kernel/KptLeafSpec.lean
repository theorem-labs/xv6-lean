import Xv6.Kernel.KptLeafDefs

namespace Xv6.Kernel.KptLeaf
open MachCSL.Machine LeanPaperStock.Functions

structure WordSpec : Prop where
  flags : ∀ ppn permission a d,
    PteCanonical.flags (word ppn permission a d) = flagByte permission a d
  ppn : ∀ ppn permission a d, PPN_of_PTE (word ppn permission a d) = ppn
  extensions : ∀ ppn permission a d, ext_bits_of_PTE (word ppn permission a d) = 0#10
  leaf : ∀ ppn permission a d, PteCanonical.Leaf (word ppn permission a d)
  setAD : ∀ ppn permission a d a' d',
    PteCanonical.setAD (word ppn permission a d) (if a' then 1#1 else 0#1)
      (if d' then 1#1 else 0#1) = word ppn permission a' d'
  canonical : ∀ ppn permission a d,
    PteCanonical.canon (word ppn permission a d) = word ppn permission false false

structure PlanSpec : Prop where
  permission : ∀ permission a d access, Supported access → Allows permission access →
    ∀ mxr doSum,
    check_PTE_permission access .Supervisor mxr doSum (flagByte permission a d) 0#10 () =
      pure (.PTE_Check_Success ())
  valid : ∀ rs permission a d,
    MachCSL.Logic.RegisterPlan.Returns [] rs (pte_is_invalid (flagByte permission a d) 0#10) false rs
  check : ∀ rs ppn permission a d vpn address access,
    Supported access → Allows permission access → ∀ mxr doSum,
    MachCSL.Logic.RegisterPlan.Returns [] rs
      (program ppn permission a d vpn address access mxr doSum) (.Ok (ppn, .PBMT_PMA, ())) rs

end Xv6.Kernel.KptLeaf
