import Xv6.Kernel.TlbWindowDefs

namespace Xv6.Kernel.TlbWindow
open TlbCoherence MachCSL.Machine

structure Spec : Prop where
  previous : ∀ asid previous current tlb,
    TlbCoherence.Coherent asid previous tlb → Coherent asid previous current tlb
  current : ∀ asid previous current tlb,
    TlbCoherence.Coherent asid current tlb → Coherent asid previous current tlb
  swap : ∀ asid previous current tlb,
    Coherent asid previous current tlb → Coherent asid current previous tlb
  collapse : ∀ asid tree tlb, Coherent asid tree tree tlb ↔ TlbCoherence.Coherent asid tree tlb
  canon_current : ∀ asid previous current other tlb,
    PtTree.canon current = PtTree.canon other →
    Coherent asid previous current tlb → Coherent asid previous other tlb
  canon_previous : ∀ asid previous other current tlb,
    PtTree.canon previous = PtTree.canon other →
    Coherent asid previous current tlb → Coherent asid other current tlb
  fill_current : ∀ asid previous current tlb vpn p2 p1 p0 word,
    PtTree.Maps current vpn p2 p1 p0 → Variant p0 word →
    Coherent asid previous current tlb → Coherent asid previous current (filled tlb asid vpn p2 p1 word)
  fill_previous : ∀ asid previous current tlb vpn p2 p1 p0 word,
    PtTree.Maps previous vpn p2 p1 p0 → Variant p0 word →
    Coherent asid previous current tlb → Coherent asid previous current (filled tlb asid vpn p2 p1 word)
  set_leaf_current : ∀ asid previous current tlb vpn p2 p1 p0 a d,
    PtTree.Maps current vpn p2 p1 p0 → Coherent asid previous current tlb →
    Coherent asid previous (PtTree.setLeaf current vpn (PteCanonical.setAD p0 a d)) tlb
  set_leaf_previous : ∀ asid previous current tlb vpn p2 p1 p0 a d,
    PtTree.Maps previous vpn p2 p1 p0 → Coherent asid previous current tlb →
    Coherent asid (PtTree.setLeaf previous vpn (PteCanonical.setAD p0 a d)) current tlb

end Xv6.Kernel.TlbWindow
