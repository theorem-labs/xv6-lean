import MachCSL.Logic.FsDurAllocFamilyProofs
import MachCSL.Logic.FsDurBytesLedgerProofs

namespace MachCSL.Logic.FsDurAlloc
open Iris Iris.Std Iris.BI Xv6.Fs DurableState FsDurBytes

theorem selected_lookup {A : Type} (slots : List A) (maps : A → ByteMap) (a : Int) (v : MachCSL.Memory.Byte)
    (found : (selected slots maps)[a]? = some v) : ∃ x, x ∈ slots ∧ (maps x)[a]? = some v := by
  induction slots with
  | nil => cases found
  | cons x xs ih =>
    change (leftUnion (maps x) (selected xs maps))[a]? = some v at found
    rw [leftUnion_lookup] at found
    cases head : (maps x)[a]? with
    | some w =>
      rw [head, Option.orElse_some] at found
      exact ⟨x, by simp, head.trans found⟩
    | none =>
      rw [head, Option.orElse_none] at found
      obtain ⟨y, mem, get⟩ := ih found
      exact ⟨y, List.mem_cons_of_mem x mem, get⟩

theorem selected_submap {A : Type} (whole : ByteMap) (slots : List A) (maps : A → ByteMap)
    (submap : ∀ x, x ∈ slots → PartialMap.submap (M := Disk.ImageMap) (maps x) whole) :
    PartialMap.submap (M := Disk.ImageMap) (selected slots maps) whole := by
  intro a v found
  obtain ⟨x, mem, get⟩ := selected_lookup slots maps a v found
  exact submap x mem a v get

theorem selected_disjoint {A : Type} (left : ByteMap) (slots : List A) (maps : A → ByteMap)
    (separated : ∀ x, x ∈ slots → PartialMap.disjoint (M := Disk.ImageMap) left (maps x)) :
    PartialMap.disjoint (M := Disk.ImageMap) left (selected slots maps) := by
  apply (PartialMap.disjoint_iff _ _).mpr
  intro a
  cases hl : left[a]? with
  | none => exact Or.inl hl
  | some v =>
    right
    cases hr : (selected slots maps)[a]? with
    | none => exact hr
    | some w =>
      obtain ⟨x, mem, get⟩ := selected_lookup slots maps a w hr
      have h := (PartialMap.disjoint_iff _ _).mp (separated x mem) a
      rcases h with absent | absent
      · change left[a]? = none at absent; rw [hl] at absent; cases absent
      · change (maps x)[a]? = none at absent; rw [get] at absent; cases absent

variable {GF : BundledGFunctors} (view : FsView.View GF)

theorem selected_ledger {A : Type} (slots : List A) (maps : A → ByteMap)
    (nodup : slots.Nodup)
    (separated : ∀ x y, x ∈ slots → y ∈ slots → x ≠ y →
      PartialMap.disjoint (M := Disk.ImageMap) (maps x) (maps y)) :
    byteLedger view (selected slots maps) ⊣⊢ bigSepL (fun _ x => byteLedger view (maps x)) slots := by
  induction slots with
  | nil =>
    simp only [selected, List.foldr_nil, byteLedger, BigSepM.bigSepM_empty.to_eq, BigSepL.bigSepL_nil.to_eq]
    exact .rfl
  | cons x xs ih =>
    have nd := List.nodup_cons.mp nodup
    have split := selected_disjoint (maps x) xs maps (fun y hy =>
      separated x y (by simp) (by simp [hy]) (fun same => nd.1 (same ▸ hy)))
    have tail := ih nd.2 (fun y z hy hz ne => separated y z (by simp [hy]) (by simp [hz]) ne)
    change byteLedger view (leftUnion (maps x) (selected xs maps)) ⊣⊢ _
    rw [(byteLedger_union view _ _ split).to_eq, tail.to_eq, BigSepL.bigSepL_cons.to_eq]
    exact .rfl

theorem ledger_carve {A : Type} (whole : ByteMap) (slots : List A) (maps : A → ByteMap)
    (nodup : slots.Nodup)
    (submap : ∀ x, x ∈ slots → PartialMap.submap (M := Disk.ImageMap) (maps x) whole)
    (separated : ∀ x y, x ∈ slots → y ∈ slots → x ≠ y →
      PartialMap.disjoint (M := Disk.ImageMap) (maps x) (maps y)) (frame : IProp GF) :
    byteLedger view whole ∗ frame ⊢ bigSepL (fun _ x => byteLedger view (maps x)) slots ∗
      byteLedger view (PartialMap.difference (M := Disk.ImageMap) whole (selected slots maps)) ∗ frame := by
  have split := byteLedger_union view (selected slots maps)
    (PartialMap.difference (M := Disk.ImageMap) whole (selected slots maps))
    (LawfulPartialMap.disjoint_difference_right (M := Disk.ImageMap))
  unfold leftUnion at split
  have cancel := LawfulPartialMap.union_difference_cancel (M := Disk.ImageMap) (selected_submap whole slots maps submap)
  change PartialMap.union (M := Disk.ImageMap) (selected slots maps)
    (PartialMap.difference (M := Disk.ImageMap) whole (selected slots maps)) = whole at cancel
  rw [cancel] at split
  rw [(selected_ledger view slots maps nodup separated).to_eq] at split
  iintro ⟨Hwhole, Hframe⟩
  ihave ⟨Hslots, Hrest⟩ := split.mp $$ Hwhole
  iframe Hslots Hrest Hframe

theorem block_ledger_cut (state : State) disk (bytes : Snapshot.Bytes state disk) (frame : IProp GF) :
    blockLedger view disk ∗ frame ⊢ slotLedger view state disk ∗
      byteLedger view (PartialMap.difference (M := Disk.ImageMap)
        (flatten disk) (selected (family state) (fpMap state disk))) ∗ frame := by
  rw [← (flatten_blocks view disk bytes.blockSize).to_eq]
  have cut := ledger_carve view (flatten disk) (family state) (fpMap state disk)
    (family_nodup state) (fun x mem => (fp_ok state disk x bytes ((family_mem state x).mp mem)).1)
    (fun x y hx hy ne => fp_disjoint state disk x y bytes ((family_mem state x).mp hx) ((family_mem state y).mp hy) ne) frame
  have runs : bigSepL (fun _ x => byteLedger view (fpMap state disk x)) (family state) ⊣⊢
      slotLedger view state disk := by
    unfold slotLedger
    constructor
    · exact BigSepL.bigSepL_mono (fun _ => (byteRange_run view _ _ _).mpr)
    · exact BigSepL.bigSepL_mono (fun _ => (byteRange_run view _ _ _).mp)
  rw [runs.to_eq] at cut
  exact cut

theorem carveSpec : CarveSpec view where
  carve := ledger_carve view
  blocks := block_ledger_cut view

end MachCSL.Logic.FsDurAlloc
