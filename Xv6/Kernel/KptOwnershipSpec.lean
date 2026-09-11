import Xv6.Kernel.KptOwnershipDefs

namespace Xv6.Kernel.KptOwnership
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

/-- Geometry/enumeration obligations for the source representation. -/
structure GeometrySpec : Prop where
  pageBase_value : ∀ b, (pageBase b).toNat = b.toNat * 4096
  pageBase_aligned : ∀ b, (pageBase b).toNat % pageSize = 0
  valid_nodeData : ∀ b, PageValid (pageBase b) → NodeData b
  valid_ne_zero : ∀ p, PageValid p → p ≠ 0#64
  index_lookup : ∀ i : Index, indices[i.toNat]? = some i
  indices_nodup : indices.Nodup
  indices_length : indices.length = 512

/-- Exact spatial accessors. Replacement resources must be supplied to each
returned wand; there is no assumed restoration or distinct-page premise. -/
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  slot_timeless : ∀ era tier a dq w, Timeless (slotOwn capacity era tier a dq w)
  node_timeless : ∀ era b, Timeless (nodeClaim capacity era b)
  node_persistent : ∀ era b, Persistent (nodeClaim capacity era b)
  page_timeless : ∀ era tier dq t, Timeless (pageOwn capacity era tier dq t)
  tree_timeless : ∀ era tier depth dq t, Timeless (treeOwn capacity era tier depth dq t)
  kids_timeless : ∀ era tier depth dq t, Timeless (kidsOwn capacity era tier depth dq t)
  slot_forget : ∀ era tier a dq w,
    iprop(slotOwn capacity era tier a dq w ⊢ rawWord capacity era a dq w)
  slot_aligned : ∀ era tier a dq w,
    iprop(slotOwn capacity era tier a dq w ⊢ ⌜is_aligned_paddr (.Physaddr a) 8 = true⌝)
  slot_ram : ∀ era tier a dq w,
    iprop(slotOwn capacity era tier a dq w ⊢ ⌜Tso.AddrIsRAM a⌝)
  slot_ram7 : ∀ era tier a dq w,
    iprop(slotOwn capacity era tier a dq w ⊢ ⌜Tso.AddrIsRAM (addressAdd a 7)⌝)
  tree_page_valid : ∀ era tier depth dq t,
    iprop(treeOwn capacity era tier depth dq t ⊢ ⌜PageValid (pageBase (PtTree.base t))⌝)
  page_access_ro : ∀ era tier dq t i,
    iprop(pageOwn capacity era tier dq t ⊢
      slotOwn capacity era tier (PtTree.slotAddress (PtTree.base t) i) dq (PtTree.entries t i) ∗
      (slotOwn capacity era tier (PtTree.slotAddress (PtTree.base t) i) dq (PtTree.entries t i) -∗
        pageOwn capacity era tier dq t))
  page_access : ∀ era tier dq t i,
    iprop(pageOwn capacity era tier dq t ⊢
      slotOwn capacity era tier (PtTree.slotAddress (PtTree.base t) i) dq (PtTree.entries t i) ∗
      (∀ w', slotOwn capacity era tier (PtTree.slotAddress (PtTree.base t) i) dq w' -∗
        pageOwn capacity era tier dq (PtTree.updateEntry t i w')))
  kids_access_ro : ∀ era tier depth dq t i c, PtTree.children t i = some c →
    iprop(kidsOwn capacity era tier depth dq t ⊢ treeOwn capacity era tier depth dq c ∗
      (treeOwn capacity era tier depth dq c -∗ kidsOwn capacity era tier depth dq t))
  kids_access : ∀ era tier depth dq t i c, PtTree.children t i = some c →
    iprop(kidsOwn capacity era tier depth dq t ⊢ treeOwn capacity era tier depth dq c ∗
      (∀ c', treeOwn capacity era tier depth dq c' -∗
        kidsOwn capacity era tier depth dq (PtTree.updateChild t i (some c'))))
  path_ro : ∀ era tier dq t vpn p2 p1 p0, PtTree.Maps t vpn p2 p1 p0 →
    iprop(treeOwn capacity era tier 2 dq t ⊢
      slotOwn capacity era tier (PtTree.addr2 t vpn) dq p2 ∗
      slotOwn capacity era tier (PtTree.addr1 p2 vpn) dq p1 ∗
      slotOwn capacity era tier (PtTree.addr0 p1 vpn) dq p0 ∗
      (slotOwn capacity era tier (PtTree.addr2 t vpn) dq p2 -∗
        slotOwn capacity era tier (PtTree.addr1 p2 vpn) dq p1 -∗
        slotOwn capacity era tier (PtTree.addr0 p1 vpn) dq p0 -∗ treeOwn capacity era tier 2 dq t))
  path_update : ∀ era tier dq t vpn p2 p1 p0, PtTree.Maps t vpn p2 p1 p0 →
    iprop(treeOwn capacity era tier 2 dq t ⊢
      slotOwn capacity era tier (PtTree.addr2 t vpn) dq p2 ∗
      slotOwn capacity era tier (PtTree.addr1 p2 vpn) dq p1 ∗
      slotOwn capacity era tier (PtTree.addr0 p1 vpn) dq p0 ∗
      (∀ w', slotOwn capacity era tier (PtTree.addr2 t vpn) dq p2 -∗
        slotOwn capacity era tier (PtTree.addr1 p2 vpn) dq p1 -∗
        slotOwn capacity era tier (PtTree.addr0 p1 vpn) dq w' -∗
        treeOwn capacity era tier 2 dq (PtTree.setLeaf t vpn w')))

end Xv6.Kernel.KptOwnership
