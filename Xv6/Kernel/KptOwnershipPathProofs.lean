import Xv6.Kernel.KptOwnershipPageProofs

namespace Xv6.Kernel.KptOwnership
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)

theorem path_ro tier dq t vpn p2 p1 p0 (mapped : PtTree.Maps t vpn p2 p1 p0) :
    iprop(treeOwn capacity era tier 2 dq t ⊢
      slotOwn capacity era tier (PtTree.addr2 t vpn) dq p2 ∗
      slotOwn capacity era tier (PtTree.addr1 p2 vpn) dq p1 ∗
      slotOwn capacity era tier (PtTree.addr0 p1 vpn) dq p0 ∗
      (slotOwn capacity era tier (PtTree.addr2 t vpn) dq p2 -∗
        slotOwn capacity era tier (PtTree.addr1 p2 vpn) dq p1 -∗
        slotOwn capacity era tier (PtTree.addr0 p1 vpn) dq p0 -∗ treeOwn capacity era tier 2 dq t)) := by
  rcases mapped with ⟨c1,c0,hc1,hc0,hp2,hp1,hp0,hb1,hb0,_⟩
  simp only [PtTree.addr2, PtTree.addr1, PtTree.addr0]
  rw [hb1, hb0, ← hp2, ← hp1, ← hp0]
  iintro H
  isimp only [tree_succ] at H
  icases H with ⟨Hpage2,Hkids2⟩
  ihave ⟨H2,Hclose2⟩ := page_access_ro capacity era tier dq t (PtTree.index 2 vpn) $$ Hpage2
  ihave ⟨Htree1,Hkidsclose2⟩ := kids_access_ro capacity era tier 1 dq t (PtTree.index 2 vpn) c1 hc1 $$ Hkids2
  isimp only [tree_succ] at Htree1
  icases Htree1 with ⟨Hpage1,Hkids1⟩
  ihave ⟨H1,Hclose1⟩ := page_access_ro capacity era tier dq c1 (PtTree.index 1 vpn) $$ Hpage1
  ihave ⟨Htree0,Hkidsclose1⟩ := kids_access_ro capacity era tier 0 dq c1 (PtTree.index 1 vpn) c0 hc0 $$ Hkids1
  isimp only [tree_zero] at Htree0
  icases Htree0 with ⟨Hpage0,_⟩
  ihave ⟨H0,Hclose0⟩ := page_access_ro capacity era tier dq c0 (PtTree.index 0 vpn) $$ Hpage0
  iframe H2 H1 H0
  iintro H2 H1 H0
  isimp only [tree_succ]
  isplitl [Hclose2 H2]
  · iapply Hclose2 $$ H2
  · iapply Hkidsclose2
    isimp only [tree_succ]
    isplitl [Hclose1 H1]
    · iapply Hclose1 $$ H1
    · iapply Hkidsclose1
      isimp only [tree_zero]
      isplitl
      · iapply Hclose0 $$ H0
      · itrivial

theorem path_update tier dq t vpn p2 p1 p0 (mapped : PtTree.Maps t vpn p2 p1 p0) :
    iprop(treeOwn capacity era tier 2 dq t ⊢
      slotOwn capacity era tier (PtTree.addr2 t vpn) dq p2 ∗
      slotOwn capacity era tier (PtTree.addr1 p2 vpn) dq p1 ∗
      slotOwn capacity era tier (PtTree.addr0 p1 vpn) dq p0 ∗
      (∀ w', slotOwn capacity era tier (PtTree.addr2 t vpn) dq p2 -∗
        slotOwn capacity era tier (PtTree.addr1 p2 vpn) dq p1 -∗
        slotOwn capacity era tier (PtTree.addr0 p1 vpn) dq w' -∗
        treeOwn capacity era tier 2 dq (PtTree.setLeaf t vpn w'))) := by
  rcases mapped with ⟨c1,c0,hc1,hc0,hp2,hp1,hp0,hb1,hb0,_⟩
  simp only [PtTree.addr2, PtTree.addr1, PtTree.addr0]
  rw [hb1, hb0, ← hp2, ← hp1, ← hp0]
  iintro H
  isimp only [tree_succ] at H
  icases H with ⟨Hpage2,Hkids2⟩
  ihave ⟨H2,Hclose2⟩ := page_access_ro capacity era tier dq t (PtTree.index 2 vpn) $$ Hpage2
  ihave ⟨Htree1,Hkidsclose2⟩ := kids_access capacity era tier 1 dq t (PtTree.index 2 vpn) c1 hc1 $$ Hkids2
  isimp only [tree_succ] at Htree1
  icases Htree1 with ⟨Hpage1,Hkids1⟩
  ihave ⟨H1,Hclose1⟩ := page_access_ro capacity era tier dq c1 (PtTree.index 1 vpn) $$ Hpage1
  ihave ⟨Htree0,Hkidsclose1⟩ := kids_access capacity era tier 0 dq c1 (PtTree.index 1 vpn) c0 hc0 $$ Hkids1
  isimp only [tree_zero] at Htree0
  icases Htree0 with ⟨Hpage0,_⟩
  ihave ⟨H0,Hclose0⟩ := page_access capacity era tier dq c0 (PtTree.index 0 vpn) $$ Hpage0
  iframe H2 H1 H0
  iintro %w' H2 H1 H0
  isimp only [PtTree.setLeaf, hc1, hc0, tree_succ, page_update_child]
  isplitl [Hclose2 H2]
  · iapply Hclose2 $$ H2
  · iapply Hkidsclose2
    isimp only [tree_succ, page_update_child]
    isplitl [Hclose1 H1]
    · iapply Hclose1 $$ H1
    · iapply Hkidsclose1
      isimp only [tree_zero]
      isplitl
      · iapply Hclose0 $$ H0
      · itrivial

end Xv6.Kernel.KptOwnership
