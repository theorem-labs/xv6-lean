import Xv6.Kernel.KernelTextBootProofs
import Xv6.Kernel.KernelTextDatumLink

namespace Xv6.Kernel.KernelTextBoot
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
attribute [local irreducible] descriptors
variable {GF : BundledGFunctors} (capacity : Capacity GF)

def physicalRun (era : Era.Record) (w : BootWindow.Word) : IProp GF :=
  iprop(TsoRead.byteWindow capacity.machine.era.heap.ledger era.heap w.address w.size .discard w.value ∗
    TsoRead.pristineWindow capacity.machine.era.heap.ledger era.timestamps w.address w.size)

instance physicalRun_persistent era w : Persistent (physicalRun capacity era w) := by
  letI := capacity.machine.era.heap.ledger.bytes
  letI := capacity.machine.era.heap.ledger.timestamps
  unfold physicalRun TsoRead.byteWindow TsoRead.pristineWindow TsoRead.pristineByte Tso.physBytePointsto
  infer_instance

theorem persist_word era (w : BootWindow.Word) :
    iprop(TsoStore.storedWindow (storeCapacity capacity) (storeNames era) w.address w.size w.value 0 ⊢
      |==> physicalRun capacity era w) := by
  iintro H
  ihave ⟨Hb, Ht⟩ := (BootWindow.storedWindow_split (storeCapacity capacity) (storeNames era)
    w.address w.size w.value 0).mp $$ H
  have times := TsoRead.pristine_window_mint capacity.machine.era.heap.ledger era.timestamps w.address w.size
  change iprop(BootWindow.timeWindow capacity.machine.era.heap.ledger era.timestamps w.address w.size 0 ⊢
    |==> TsoRead.pristineWindow capacity.machine.era.heap.ledger era.timestamps w.address w.size) at times
  isimp only [storeCapacity, MycpuBootResources.storeCapacity, storeNames, MycpuBootResources.storeNames,
    Era.Record.tsoNames] at Ht
  isimp only [storeCapacity, MycpuBootResources.storeCapacity, storeNames, MycpuBootResources.storeNames,
    Era.Record.tsoNames] at Hb
  imod times $$ Ht with Ht
  iunfold TsoRead.byteWindow at Hb
  ihave Hb : (|==> [∗list] j ∈ List.range w.size,
      Tso.physBytePointsto capacity.machine.era.heap.ledger era.heap (addressAdd w.address j)
        .discard (nthByte w.value j)) $$ [Hb]
  · iapply BigSepL.bigSepL_bupd
    iapply BigSepL.bigSepL_mono $$ Hb
    intro _ j _
    unfold Tso.physBytePointsto
    iintro ⟨Hb, %isRam⟩
    letI := capacity.machine.era.heap.ledger.bytes
    imod ghost_map_elem_persist (GF := GF) (K := PhysicalAddress) (V := Byte) (H := Tso.AddressMap)
      era.heap (addressAdd w.address j) (.own 1) (nthByte w.value j) $$ Hb with Hb
    imodintro
    iframe Hb
    ipureintro; exact isRam
  imod Hb with Hb
  imodintro
  unfold physicalRun TsoRead.byteWindow
  iframe

theorem physical_lookup era (w : BootWindow.Word) (j : Nat) (inside : j < w.size) :
    iprop(physicalRun capacity era w ⊢
      KernelTextDatum.rawByte capacity era (addressAdd w.address j) .discard (nthByte w.value j) ∗
      KernelTextDatum.pristine capacity era (addressAdd w.address j)) := by
  unfold physicalRun TsoRead.byteWindow TsoRead.pristineWindow
  iintro ⟨Hb, Ht⟩
  have lookup : (List.range w.size)[j]? = some j := by simp [inside]
  ihave ⟨Hb, _⟩ := BigSepL.bigSepL_lookup lookup $$ Hb
  ihave Ht := BigSepL.bigSepL_lookup lookup $$ Ht
  iframe
  unfold KernelTextDatum.rawByte Heap.pointsto pointsTo
  iexact Hb

theorem physical_text era :
    iprop(([∗list] w ∈ descriptors, physicalRun capacity era w) ⊢ KernelTextImage.physicalText capacity era) := by
  iintro #H
  iunfold KernelTextImage.physicalText
  iintro %a %b %found
  obtain ⟨run, member, j, inside, rfl, rfl⟩ := KernelTextImage.lookup_listed a b found
  have selected : descriptor run ∈ descriptors := by rw [descriptors]; exact List.mem_map.mpr ⟨run, member, rfl⟩
  obtain ⟨i, lookup⟩ := List.mem_iff_getElem?.mp selected
  ihave Hrun := BigSepL.bigSepL_lookup lookup $$ H
  have getByte := physical_lookup capacity era (descriptor run) j inside
  rw [bytes run member j inside] at getByte
  change iprop(physicalRun capacity era (descriptor run) ⊢
      KernelTextDatum.rawByte capacity era (addressAdd (address run.base) j) .discard (value (run.byte j)) ∗
      KernelTextDatum.pristine capacity era (addressAdd (address run.base) j)) at getByte
  rw [address_add] at getByte
  iapply getByte $$ Hrun

theorem persist era : iprop(rawText capacity era ⊢ |==> KernelTextImage.physicalText capacity era) := by
  unfold rawText
  iintro H
  ihave H : (|==> [∗list] w ∈ descriptors, physicalRun capacity era w) $$ [H]
  · iapply BigSepL.bigSepL_bupd
    iapply BigSepL.bigSepL_mono $$ H
    intro _ w _
    exact persist_word capacity era w
  imod H with H
  imodintro
  iapply physical_text capacity era $$ H

theorem produce era g memory diskBytes
    (facts : BootFacts Xv6.Machine.bootImage g) (decoded : FiniteMap.decode memory = g.memory) :
    iprop(Era.bootClients capacity.machine.era era memory g diskBytes ⊢ |==>
      KernelTextImage.physicalText capacity era ∗ retained capacity era memory g diskBytes) := by
  exact (extract capacity era g memory diskBytes facts decoded).trans
    (sep_mono (persist capacity era) (.refl _))

/-- Explicitly framed combined update; produce itself returns the untouched
remainder beside the pending text update, matching its approved signature. -/
theorem produce_update era g memory diskBytes
    (facts : BootFacts Xv6.Machine.bootImage g) (decoded : FiniteMap.decode memory = g.memory) :
    iprop(Era.bootClients capacity.machine.era era memory g diskBytes ⊢ |==>
      (KernelTextImage.physicalText capacity era ∗ retained capacity era memory g diskBytes)) :=
  (produce capacity era g memory diskBytes facts decoded).trans bupd_frame_right

end Xv6.Kernel.KernelTextBoot
