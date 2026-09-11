import Xv6.Kernel.PtTreeCanonProofs
import Xv6.Kernel.PtTreePointerProofs

namespace Xv6.Kernel.PtTree

/-- All source-pure tree contracts, with actual generated validation semantics. -/
theorem actual : Spec :=
  ⟨outcome_unique, valid_invalid, index_injective, address_value, address_aligned,
    maps_det, maps_blocks_excl, set_leaf_maps_self, set_leaf_maps_other,
    set_leaf_blocks, set_ad_valid_leaf, maps_canon, maps_canon_inv, maps_across,
    canon_set_leaf⟩

/-- Raw pointer plans preserve arbitrary G/RSW/PPN bits and all register files. -/
theorem actualPointer : PointerSpec :=
  ⟨pointer_ext_zero, pointer_flags, pointer_validation_plan, global_setAD⟩

end Xv6.Kernel.PtTree
