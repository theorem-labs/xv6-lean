import Xv6.Kernel.TlbCoherenceDefs

/-! Exact two-tree cache provenance in the SATP-switch window.
Source: pinned PtTree.v:1999–2112. Each occupied slot may originate in
either tree; provenance is retained per entry, not chosen for the vector. -/
namespace Xv6.Kernel.TlbWindow
open TlbCoherence

def Coherent (asid : Asid) (previous current : PtTree.Tree) (tlb : Tlb) : Prop :=
  ∀ query ent, tlb[index query]? = some (some ent) →
    CacheOf asid previous query ent ∨ CacheOf asid current query ent

end Xv6.Kernel.TlbWindow
