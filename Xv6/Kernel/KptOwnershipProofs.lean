import Xv6.Kernel.KptOwnershipPathProofs

namespace Xv6.Kernel.KptOwnership
open Iris

/-- Native Iris implementation of every approved spatial contract. -/
theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity where
  slot_timeless := slot_timeless capacity
  node_timeless := node_timeless capacity
  node_persistent := node_persistent capacity
  page_timeless := page_timeless capacity
  tree_timeless := tree_timeless capacity
  kids_timeless := kids_timeless capacity
  slot_forget := slot_forget capacity
  slot_aligned := slot_aligned capacity
  slot_ram := slot_ram capacity
  slot_ram7 := slot_ram7 capacity
  tree_page_valid := tree_page_valid capacity
  page_access_ro := page_access_ro capacity
  page_access := page_access capacity
  kids_access_ro := kids_access_ro capacity
  kids_access := kids_access capacity
  path_ro := path_ro capacity
  path_update := path_update capacity

end Xv6.Kernel.KptOwnership
