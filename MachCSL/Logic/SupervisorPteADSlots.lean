import MachCSL.Logic.SupervisorPteADDefs
import MachCSL.Logic.TsoPinnedReadProofs

namespace MachCSL.Logic.SupervisorPteAD
open Iris Iris.BI MachCSL.Machine MachCSL.Memory

/-- Finite existential collection; the chosen function is relevant only on
this duplicate-free list. No ownership is created or discarded. -/
theorem collect_floors {GF : BundledGFunctors} (Φ : Nat → Nat → IProp GF)
    (keys : List Nat) (unique : keys.Nodup) :
    iprop(([∗list] j ∈ keys, ∃ floor : Nat, Φ j floor) ⊢
      ∃ floors : Nat → Nat, [∗list] j ∈ keys, Φ j (floors j)) := by
  induction keys with
  | nil =>
    iintro _
    iexists (fun _ => 0)
    iapply BigSepL.bigSepL_nil.mpr
    itrivial
  | cons j keys ih =>
    rcases List.nodup_cons.mp unique with ⟨absent, unique⟩
    simp only [BigSepL.bigSepL_cons.to_eq]
    iintro ⟨⟨%floor, Hhead⟩, Htail⟩
    ihave ⟨%floors, Htail⟩ := ih unique $$ Htail
    iexists (fun k => if k = j then floor else floors k)
    isplitl [Hhead]
    · simp only [↓reduceIte]
      iexact Hhead
    · iapply BigSepL.bigSepL_mono (fun {_ k} found => ?_) $$ Htail
      have different : k ≠ j := by
        intro same
        subst k
        exact absent (List.mem_iff_getElem?.mpr ⟨_, found⟩)
      simp only [different, ↓reduceIte]
      exact .rfl

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)

def anchors (era : Era.Record) (address : BitVec 64) (bound : Nat)
    (floors : Nat → Nat) : IProp GF :=
  iprop([∗list] j ∈ List.range 8,
    ⌜floors j ≤ bound⌝ ∗
      TsoPinnedRead.slotAnchor capacity.era.tso era.tsoNames (addressAdd address j) (floors j))

/-- Exposes only the original per-byte floors; the publication anchors and
bounds remain available to reconstruct the exact original slot family. -/
theorem slot_open (era : Era.Record) (address word : BitVec 64) (bound : Nat)
    (sets : Nat → Tso.ByteSet) :
    iprop(TsoPinnedReadWP.slot capacity era address 8 (.own 1) (nthByte word) bound sets ⊢
      ∃ floors : Nat → Nat,
        TsoPinnedWriteWP.pinWindow capacity era address word (.own 1) floors sets ∗
        anchors capacity era address bound floors) := by
  unfold TsoPinnedReadWP.slot TsoPinnedRead.slotBytes
  iintro H
  ihave ⟨%floors, H⟩ := collect_floors _ (List.range 8) List.nodup_range $$ H
  iexists floors
  unfold TsoPinnedWriteWP.pinWindow TsoPinnedStore.pinWindow anchors MemoryWriteWP.storeCapacity MemoryWriteWP.storeNames Era.Record.tsoNames Era.Capacity.tso
  rw [← BigSepL.bigSepL_sep_eqv.to_eq]
  iapply BigSepL.bigSepL_mono (fun {_ j} _ => ?_) $$ H
  iintro ⟨%time, %bound, Hpin, Hanchor⟩
  isplitl [Hpin]
  · iexists time; iexact Hpin
  · iframe Hanchor; ipureintro; exact bound

/-- Reconstruct the full source slot after an authored write, retaining the
same floor, publication anchor, and bound at every byte. -/
theorem slot_close (era : Era.Record) (address word : BitVec 64) (time bound : Nat)
    (floors : Nat → Nat) (sets : Nat → Tso.ByteSet) :
    iprop(TsoPinnedWriteWP.storedWindow capacity era address word time floors sets ∗
      anchors capacity era address bound floors ⊢
      TsoPinnedReadWP.slot capacity era address 8 (.own 1) (nthByte word) bound sets) := by
  unfold TsoPinnedWriteWP.storedWindow TsoPinnedStore.storedWindow anchors
    TsoPinnedReadWP.slot TsoPinnedRead.slotBytes MemoryWriteWP.storeCapacity MemoryWriteWP.storeNames Era.Record.tsoNames Era.Capacity.tso
  rw [← BigSepL.bigSepL_sep_eqv.to_eq]
  apply BigSepL.bigSepL_mono
  intro i j found
  iintro ⟨Hpin, %bound, Hanchor⟩
  iexists (floors j), time
  iframe Hpin Hanchor
  ipureintro; exact bound

end MachCSL.Logic.SupervisorPteAD
