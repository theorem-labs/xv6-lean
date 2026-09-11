import Xv6.Kernel.KptReadEventPure
import Xv6.Kernel.KptSharedProofs

namespace Xv6.Kernel.KptReadEvent
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF) (ownership : KptOwnership.Spec capacity)

include ownership

/-- Select one actual current slot and retain the complete tree restoration
wand. Canonical snapshot equality fixes the upper words and page addresses. -/
theorem path_access era tier dq tree current vpn p2 p1 p0 level
    (mapped : PtTree.Maps tree vpn p2 p1 p0)
    (same : PtTree.canon tree = PtTree.canon current) :
    iprop(KptOwnership.treeOwn capacity era tier 2 dq current ⊢ ∃ word,
      ⌜ReadFact (reference p2 p1 p0 level) word⌝ ∗
      KptOwnership.slotOwn capacity era tier (address tree vpn p2 p1 level) dq word ∗
      (KptOwnership.slotOwn capacity era tier (address tree vpn p2 p1 level) dq word -∗
        KptOwnership.treeOwn capacity era tier 2 dq current)) := by
  have bases := congrArg PtTree.base same
  change PtTree.base tree = PtTree.base current at bases
  have addr2 : PtTree.addr2 current vpn = PtTree.addr2 tree vpn := by
    unfold PtTree.addr2
    rw [bases]
  obtain ⟨q0,currentMaps,canonical⟩ := PtTree.maps_across tree current vpn p2 p1 p0 same mapped
  have relation : ReadFact p0 q0 := readFact_leaf p0 q0 (mapped_leaf tree vpn p2 p1 p0 mapped) canonical
  have levels : level = ⟨0, by decide⟩ ∨ level = ⟨1, by decide⟩ ∨ level = ⟨2, by decide⟩ := by
    rcases level with ⟨n,hn⟩
    have ncases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases ncases with rfl | rfl | rfl <;> simp
  iintro Htree
  ihave ⟨Hslot2,Hslot1,Hslot0,Hrestore⟩ := ownership.path_ro era tier dq current vpn p2 p1 q0 currentMaps $$ Htree
  isimp only [addr2] at Hslot2 Hrestore
  rcases levels with rfl | rfl | rfl <;> simp only [address, reference]
  · iexists q0
    isplit
    · ipureintro; exact relation
    iframe Hslot0
    iintro Hslot0
    iapply Hrestore $$ Hslot2 Hslot1 Hslot0
  · iexists p1
    isplit
    · ipureintro; exact readFact_refl p1
    iframe Hslot1
    iintro Hslot1
    iapply Hrestore $$ Hslot2 Hslot1 Hslot0
  · iexists p2
    isplit
    · ipureintro; exact readFact_refl p2
    iframe Hslot2
    iintro Hslot2
    iapply Hrestore $$ Hslot2 Hslot1 Hslot0

end Xv6.Kernel.KptReadEvent
