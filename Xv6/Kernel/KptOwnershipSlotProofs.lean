import Xv6.Kernel.KptOwnershipGeometry
import MachCSL.Logic.KptGhostProofs
import MachCSL.Logic.TsoPinnedReadProofs
import MachCSL.Logic.TsoContextWordProofs

namespace Xv6.Kernel.KptOwnership
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)

instance kernelSlot_timeless B a dq w : Timeless (kernelSlot capacity era B a dq w) := by
  unfold kernelSlot TsoPinnedReadWP.slot TsoPinnedRead.slotBytes
    TsoPinnedRead.slotAnchor TsoPinnedRead.ownAnchor
  infer_instance
instance slot_timeless tier a dq w : Timeless (slotOwn capacity era tier a dq w) := by
  cases tier <;> unfold slotOwn <;> infer_instance
instance node_timeless b : Timeless (nodeClaim capacity era b) := by unfold nodeClaim; infer_instance
instance node_persistent b : Persistent (nodeClaim capacity era b) := by unfold nodeClaim; infer_instance
instance page_timeless tier dq t : Timeless (pageOwn capacity era tier dq t) := by unfold pageOwn; infer_instance
instance rawWord_timeless a dq w : Timeless (rawWord capacity era a dq w) := by unfold rawWord; infer_instance

instance tree_timeless tier depth dq t : Timeless (treeOwn capacity era tier depth dq t) := by
  induction depth generalizing t with
  | zero => unfold treeOwn; infer_instance
  | succ depth ih =>
    haveI : Timeless (kidsOwn capacity era tier depth dq t) := by
      unfold kidsOwn
      apply BigSepL.bigSepL_timeless
      intro k i found
      cases h : PtTree.children t i with
      | none => infer_instance
      | some c => exact ih c
    change Timeless (iprop(pageOwn capacity era tier dq t ∗ kidsOwn capacity era tier depth dq t))
    infer_instance

instance kids_timeless tier depth dq t : Timeless (kidsOwn capacity era tier depth dq t) := by
  unfold kidsOwn
  apply BigSepL.bigSepL_timeless
  intro k i found
  cases h : PtTree.children t i <;> infer_instance

theorem kernelSlot_forget B a dq w : kernelSlot capacity era B a dq w ⊢ rawWord capacity era a dq w := by
  unfold kernelSlot TsoPinnedReadWP.slot TsoPinnedRead.slotBytes rawWord
  simp only [Era.Capacity.tso, Era.Record.tsoNames]
  iintro ⟨Hal,Hbytes⟩
  iframe Hal
  iapply BigSepL.bigSepL_mono $$ Hbytes
  intro k j found
  iintro ⟨%floor,%time,_,H,_⟩
  iapply Tso.physLedgerPin_forget capacity.machine.era.heap.ledger ⟨era.heap, era.timestamps⟩
    (addressAdd a j) dq (nthByte w j) time floor (PteCanonical.slotSet w j) $$ H

theorem userSlot_forget ξ a dq w :
    TsoContextReadWP.wordPointsto capacity.machine era ξ a dq w ⊢ rawWord capacity era a dq w := by
  unfold TsoContextReadWP.wordPointsto TsoContextWord.pointsto rawWord
  simp only [TsoContextReadWP.contextCapacity, TsoContextReadWP.contextNames, Era.Record.tsoNames]
  iintro ⟨%aligned,Hbytes⟩
  isplit
  · ipureintro; exact (aligned_iff a).mpr aligned
  · iapply BigSepL.bigSepL_mono $$ Hbytes
    intro k j found
    unfold TsoContext.physPointsto
    iintro ⟨%time,H,_,_⟩
    iexact H

theorem slot_forget tier a dq w : slotOwn capacity era tier a dq w ⊢ rawWord capacity era a dq w := by
  cases tier with
  | kernel B => exact kernelSlot_forget capacity era B a dq w
  | user ξ => exact userSlot_forget capacity era ξ a dq w

theorem slot_aligned tier a dq w :
    slotOwn capacity era tier a dq w ⊢ iprop(⌜is_aligned_paddr (.Physaddr a) 8 = true⌝) := by
  iintro H
  ihave Hraw := slot_forget capacity era tier a dq w $$ H
  iunfold rawWord at Hraw
  icases Hraw with ⟨H,_⟩
  iexact H

theorem slot_ram_at tier a dq w j (hj : j < 8) :
    slotOwn capacity era tier a dq w ⊢ iprop(⌜Tso.AddrIsRAM (addressAdd a j)⌝) := by
  iintro H
  ihave Hraw := slot_forget capacity era tier a dq w $$ H
  iunfold rawWord at Hraw
  icases Hraw with ⟨_,Hbytes⟩
  have found : (List.range 8)[j]? = some j := by simp [hj]
  ihave Hbyte := BigSepL.bigSepL_lookup found $$ Hbytes
  iapply Tso.physBytePointsto_ram capacity.machine.era.heap.ledger era.heap (addressAdd a j) dq
    (nthByte w j) $$ Hbyte

theorem slot_ram tier a dq w : slotOwn capacity era tier a dq w ⊢ iprop(⌜Tso.AddrIsRAM a⌝) := by
  simpa only [addressAdd, BitVec.add_zero] using slot_ram_at capacity era tier a dq w 0 (by decide)

theorem slot_ram7 tier a dq w :
    slotOwn capacity era tier a dq w ⊢ iprop(⌜Tso.AddrIsRAM (addressAdd a 7)⌝) :=
  slot_ram_at capacity era tier a dq w 7 (by decide)

theorem tree_page_valid tier depth dq t :
    treeOwn capacity era tier depth dq t ⊢ iprop(⌜PageValid (pageBase (PtTree.base t))⌝) := by
  cases depth <;> unfold treeOwn pageOwn nodeClaim <;>
    iintro ⟨⟨⟨_,H,_⟩,_⟩,_⟩ <;> iexact H

end Xv6.Kernel.KptOwnership
