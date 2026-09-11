import Xv6.Kernel.KptPublishPureProofs
import Xv6.Kernel.KptOwnershipSlotProofs
import MachCSL.Logic.ContextPinMintLink

namespace Xv6.Kernel.KptPublish
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem pin_word : ∀ era a word B,
    iprop(⊢ viewZero capacity era B -∗
      ContextPinMint.pinnedWord (contextCapacity capacity) (contextNames era)
        a word B (PteCanonical.slotSet word) -∗
      KptOwnership.kernelSlot capacity era B a (.own 1) word) := by
  intro era a word B
  unfold ContextPinMint.pinnedWord KptOwnership.kernelSlot ContextPinMint.pinnedBytes
    TsoPinnedReadWP.slot TsoPinnedRead.slotBytes
  simp only [Era.Capacity.tso, Era.Record.tsoNames]
  iintro #Hview ⟨%aligned, Hbytes⟩
  isplit
  · ipureintro
    exact (KptOwnership.aligned_iff a).mpr aligned
  iapply BigSepL.bigSepL_impl $$ Hbytes
  iintro !> %k %j %lookup ⟨%time, Hpin⟩
  iexists B, time
  iframe Hpin
  isplit
  · ipureintro; exact Nat.le_refl _
  unfold TsoPinnedRead.slotAnchor
  iright; iright
  iexact Hview

theorem slot_view : ∀ era cpu ξ g a (word : BitVec 64),
    ContextPinMint.Drained cpu g →
    iprop(⊢ viewZero capacity era (g.views cpu) -∗
      heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.slotOwn capacity era (.user ξ) a (.own 1) word ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.slotOwn capacity era (.kernel (g.views cpu)) a (.own 1) word) := by
  intro era cpu ξ g a word drained
  iintro #Hview Hheap Htso Hrun Hword
  have mint : iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗ KptOwnership.slotOwn capacity era (.user ξ) a (.own 1) word ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      ContextPinMint.pinnedWord (contextCapacity capacity) (contextNames era) a word (g.views cpu) (PteCanonical.slotSet word)) :=
    ContextPinMint.word (contextCapacity capacity) (contextNames era) cpu ξ era.imageBytes g
    a word (PteCanonical.slotSet word) drained (fun j _ => slot_set_self word j)
  imod mint $$ Hheap Htso Hrun Hword with ⟨Hheap, Htso, Hrun, Hword⟩
  imodintro
  iframe Hheap Htso Hrun
  unfold KptOwnership.slotOwn
  iapply pin_word capacity era a word (g.views cpu) $$ Hview Hword

theorem slots_view : ∀ era cpu ξ g (α : Type) (indices : List α) (address : α → PhysicalAddress) (word : α → BitVec 64),
    ContextPinMint.Drained cpu g →
    iprop(⊢ viewZero capacity era (g.views cpu) -∗
      heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      slotsOwn capacity era (.user ξ) indices address word ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      slotsOwn capacity era (.kernel (g.views cpu)) indices address word) := by
  intro era cpu ξ g α indices address word drained
  induction indices with
  | nil =>
    unfold slotsOwn
    simp only [BigSepL.bigSepL_nil.to_eq]
    iintro #Hview Hheap Htso Hrun _
    imodintro
    iframe Hheap Htso Hrun
  | cons i indices ih =>
    unfold slotsOwn
    rw [BigSepL.bigSepL_cons.to_eq, BigSepL.bigSepL_cons.to_eq]
    iintro #Hview Hheap Htso Hrun ⟨Hslot, Hslots⟩
    imod slot_view capacity era cpu ξ g (address i) (word i) drained
      $$ Hview Hheap Htso Hrun Hslot with ⟨Hheap, Htso, Hrun, Hslot⟩
    have tail := ih
    unfold slotsOwn at tail
    imod tail $$ Hview Hheap Htso Hrun Hslots with ⟨Hheap, Htso, Hrun, Hslots⟩
    imodintro
    iframe Hheap Htso Hrun Hslot Hslots

theorem page_view : ∀ era cpu ξ g tree,
    ContextPinMint.Drained cpu g →
    iprop(⊢ viewZero capacity era (g.views cpu) -∗
      heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.pageOwn capacity era (.user ξ) (.own 1) tree ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.pageOwn capacity era (.kernel (g.views cpu)) (.own 1) tree) := by
  intro era cpu ξ g tree drained
  unfold KptOwnership.pageOwn
  iintro #Hview Hheap Htso Hrun ⟨Hclaim, Hslots⟩
  have gate := slots_view capacity era cpu ξ g KptOwnership.Index KptOwnership.indices
    (PtTree.slotAddress (PtTree.base tree)) (PtTree.entries tree) drained
  unfold slotsOwn at gate
  imod gate $$ Hview Hheap Htso Hrun Hslots with ⟨Hheap, Htso, Hrun, Hslots⟩
  imodintro
  iframe Hheap Htso Hrun Hclaim Hslots

theorem slot_boot : ∀ era cpu ξ g a (word : BitVec 64),
    hartAgent cpu = 0 →
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.slotOwn capacity era (.user ξ) a (.own 1) word ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.slotOwn capacity era (.kernel g.log.length) a (.own 1) word) := by
  intro era cpu ξ g a word boot
  iintro Hheap Htso Hrun Hword
  have mint : iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗ KptOwnership.slotOwn capacity era (.user ξ) a (.own 1) word ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      ContextPinMint.bootWord (contextCapacity capacity) (contextNames era) g a word (PteCanonical.slotSet word)) :=
    ContextPinMint.word_boot (contextCapacity capacity) (contextNames era) cpu ξ era.imageBytes g
    a word (PteCanonical.slotSet word) boot (fun j _ => slot_set_self word j)
  imod mint $$ Hheap Htso Hrun Hword with ⟨Hheap, Htso, Hrun, Hword⟩
  imodintro
  iframe Hheap Htso Hrun
  iunfold ContextPinMint.bootWord at Hword
  icases Hword with ⟨%aligned, Hbytes⟩
  unfold KptOwnership.slotOwn KptOwnership.kernelSlot
  isplit
  · ipureintro; exact (KptOwnership.aligned_iff a).mpr aligned
  ieval (change _ ⊢ ContextPinMint.bootBytes (contextCapacity capacity) (contextNames era) g a 8 (nthByte word) (PteCanonical.slotSet word))
  iexact Hbytes

theorem slots_boot : ∀ era cpu ξ g (α : Type) (indices : List α) (address : α → PhysicalAddress) (word : α → BitVec 64),
    hartAgent cpu = 0 →
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      slotsOwn capacity era (.user ξ) indices address word ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      slotsOwn capacity era (.kernel g.log.length) indices address word) := by
  intro era cpu ξ g α indices address word boot
  induction indices with
  | nil =>
    unfold slotsOwn
    simp only [BigSepL.bigSepL_nil.to_eq]
    iintro Hheap Htso Hrun _
    imodintro
    iframe Hheap Htso Hrun
  | cons i indices ih =>
    unfold slotsOwn
    rw [BigSepL.bigSepL_cons.to_eq, BigSepL.bigSepL_cons.to_eq]
    iintro Hheap Htso Hrun ⟨Hslot, Hslots⟩
    imod slot_boot capacity era cpu ξ g (address i) (word i) boot
      $$ Hheap Htso Hrun Hslot with ⟨Hheap, Htso, Hrun, Hslot⟩
    have tail := ih
    unfold slotsOwn at tail
    imod tail $$ Hheap Htso Hrun Hslots with ⟨Hheap, Htso, Hrun, Hslots⟩
    imodintro
    iframe Hheap Htso Hrun Hslot Hslots

theorem page_boot : ∀ era cpu ξ g tree,
    hartAgent cpu = 0 →
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.pageOwn capacity era (.user ξ) (.own 1) tree ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.pageOwn capacity era (.kernel g.log.length) (.own 1) tree) := by
  intro era cpu ξ g tree boot
  unfold KptOwnership.pageOwn
  iintro Hheap Htso Hrun ⟨Hclaim, Hslots⟩
  have gate := slots_boot capacity era cpu ξ g KptOwnership.Index KptOwnership.indices
    (PtTree.slotAddress (PtTree.base tree)) (PtTree.entries tree) boot
  unfold slotsOwn at gate
  imod gate $$ Hheap Htso Hrun Hslots with ⟨Hheap, Htso, Hrun, Hslots⟩
  imodintro
  iframe Hheap Htso Hrun Hclaim Hslots

end Xv6.Kernel.KptPublish
