import Xv6.Kernel.PtTreeDefs

namespace Xv6.Kernel.PtTree
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

/-- Pure source laws to implement. This structure is a contract, not an
instance or an assertion that the laws have already been proved. -/
structure Spec : Prop where
  outcome_unique : ∀ w a b, Outcome w a → Outcome w b → a = b
  valid_invalid : ∀ w, Valid w → Invalid w → False
  index_injective : ∀ x y, index 2 x = index 2 y → index 1 x = index 1 y →
    index 0 x = index 0 y → x = y
  address_value : ∀ b i, (slotAddress b i).toNat = b.toNat * 4096 + i.toNat * 8
  address_aligned : ∀ b i, is_aligned_paddr (.Physaddr (slotAddress b i)) 8 = true
  maps_det : ∀ t vpn p2 p1 p0 q2 q1 q0, Maps t vpn p2 p1 p0 → Maps t vpn q2 q1 q0 →
    p2 = q2 ∧ p1 = q1 ∧ p0 = q0
  maps_blocks_excl : ∀ t vpn p2 p1 p0, Maps t vpn p2 p1 p0 → Blocks t vpn → False
  set_leaf_maps_self : ∀ t vpn p2 p1 p0 w, Maps t vpn p2 p1 p0 →
    Valid w → Leaf w → NoNapot w → PbmtZero w → Maps (setLeaf t vpn w) vpn p2 p1 w
  set_leaf_maps_other : ∀ t vpn vpn' q2 q1 q0 w, vpn' ≠ vpn → Maps t vpn' q2 q1 q0 →
    Maps (setLeaf t vpn w) vpn' q2 q1 q0
  set_leaf_blocks : ∀ t vpn vpn' p2 p1 p0 w, Maps t vpn p2 p1 p0 → Blocks t vpn' →
    Blocks (setLeaf t vpn w) vpn'
  set_ad_valid_leaf : ∀ w a d, Leaf w →
    (Valid (PteCanonical.setAD w a d) ↔ Valid w)
  maps_canon : ∀ t vpn p2 p1 p0, Maps t vpn p2 p1 p0 →
    Maps (canon t) vpn p2 p1 (PteCanonical.canon p0)
  maps_canon_inv : ∀ t vpn p2 p1 w, Maps (canon t) vpn p2 p1 w →
    ∃ p0, Maps t vpn p2 p1 p0 ∧ w = PteCanonical.canon p0
  maps_across : ∀ t t' vpn p2 p1 p0, canon t = canon t' → Maps t vpn p2 p1 p0 →
    ∃ q0, Maps t' vpn p2 p1 q0 ∧ PteCanonical.canon q0 = PteCanonical.canon p0
  canon_set_leaf : ∀ t vpn p2 p1 p0 a d, Maps t vpn p2 p1 p0 →
    canon (setLeaf t vpn (PteCanonical.setAD p0 a d)) = canon t

/-- Actual validation plans must be derived from finite semantic validity,
not stored as the architectural definition of a valid PTE. -/
structure PointerSpec : Prop where
  ext_zero : ∀ w, Valid w → Pointer w → ext_bits_of_PTE w = 0#10
  flags : ∀ w, Valid w → Pointer w →
    _get_PTE_Flags_V (PteCanonical.flags w) = 1#1 ∧
    _get_PTE_Flags_A (PteCanonical.flags w) = 0#1 ∧
    _get_PTE_Flags_D (PteCanonical.flags w) = 0#1 ∧
    _get_PTE_Flags_U (PteCanonical.flags w) = 0#1
  validation_plan : ∀ w, Valid w → Pointer w → ∀ rs,
    RegisterPlan.Returns [] rs (validation w) false rs
  global_setAD : ∀ w a d, globalBit (PteCanonical.setAD w a d) = globalBit w

end Xv6.Kernel.PtTree
