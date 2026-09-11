import MachCSL.Logic.FsInodeRegionSpec
import MachCSL.Logic.FsViewProofs

namespace MachCSL.Logic.FsInodeRegion
open Iris Iris.Std Iris.CMRA Iris.BI Xv6.Fs
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance authQ_timeless g dq records : Timeless (authQ capacity g dq records) := by
  letI := capacity.record
  unfold authQ; infer_instance
instance auth_timeless g records : Timeless (auth capacity g records) := by unfold auth; infer_instance
instance fragQ_timeless g dq i record : Timeless (fragQ capacity g dq i record) := by
  letI := capacity.record
  unfold fragQ; infer_instance
instance frag_timeless g i record : Timeless (frag capacity g i record) := by unfold frag; infer_instance
instance dinodeAt_timeless g i record : Timeless (dinodeAt capacity g i record) := by unfold dinodeAt; infer_instance
instance imark_timeless g i : Timeless (imark capacity g i) := by unfold imark; infer_instance
instance out_timeless g i record : Timeless (out capacity g i record) := by unfold out; split <;> infer_instance
instance allFragments_timeless g records : Timeless (allFragments capacity g records) := by unfold allFragments; infer_instance

theorem lookup g records dq i record : auth capacity g records ∗ fragQ capacity g dq i record ⊢ ⌜records[i]? = some record⌝ := by
  letI := capacity.record
  iintro ⟨Ha, Hf⟩
  have law : iprop(⊢ auth capacity g records -∗ fragQ capacity g dq i record -∗ ⌜records[i]? = some record⌝) := ghost_map_lookup
  iapply law $$ Ha Hf

theorem frag_agree g dq1 dq2 i left right :
    iprop(fragQ capacity g dq1 i left ∗ fragQ capacity g dq2 i right ⊢ ⌜left = right⌝) := by
  letI := capacity.record
  unfold fragQ
  iintro ⟨Hl, Hr⟩
  iapply ghost_map_elem_agree (H := RecordMap) (GF := GF) g i dq1 dq2 left right $$ [$Hl $Hr]

theorem frag_split g i record (q1 q2 : Qp) : fragQ capacity g (.own (q1 + q2)) i record ⊣⊢
    fragQ capacity g (.own q1) i record ∗ fragQ capacity g (.own q2) i record := by
  letI := capacity.record
  exact Fractional.fractional (Φ := fun q : Qp => (ghost_map_elem g (.own q) i record : IProp GF)) q1 q2

theorem frag_exclusive g i left right : iprop(frag capacity g i left ∗ frag capacity g i right ⊢ False) := by
  letI := capacity.record
  unfold frag fragQ
  iintro ⟨Hl, Hr⟩
  ihave ⟨%valid, _⟩ := ghost_map_elem_valid_2 (H := RecordMap) (GF := GF) g i (.own 1) (.own 1) left right $$ [$Hl $Hr]
  ipureintro
  exact FsView.dfrac_full_invalid _ valid

theorem imark_exclusive g i : iprop(imark capacity g i ∗ imark capacity g i ⊢ False) := by
  unfold imark
  iintro ⟨⟨%left, Hl⟩, ⟨%right, Hr⟩⟩
  iapply frag_exclusive capacity g (markKey i) left right $$ [$Hl $Hr]

theorem out_allocated g i record (nonzero : record.typeZ ≠ 0) :
    out capacity g i record = dinodeAt capacity g i record := by simp [out, nonzero]
theorem out_free g i record (zero : record.typeZ = 0) :
    out capacity g i record = imark capacity g i.toNat := by simp [out, zero]

theorem allocate records : iprop(⊢ |==> ∃ g, auth capacity g records ∗ allFragments capacity g records) := by
  letI := capacity.record
  exact ghost_map_alloc (H := RecordMap) (GF := GF) records

theorem update g records i old new : iprop(auth capacity g records ∗ frag capacity g i old ⊢
    |==> (auth capacity g (records.insert i new) ∗ frag capacity g i new)) := by
  letI := capacity.record
  have same : PartialMap.insert (M := RecordMap) records i new = records.insert i new := by
    apply _root_.Std.ExtTreeMap.ext_getElem?
    intro key
    simp [Iris.Std.insert, _root_.Std.ExtTreeMap.getElem?_alter, _root_.Std.ExtTreeMap.getElem?_insert]
  rw [← same]
  iintro ⟨Ha, Hf⟩
  have law : iprop(⊢ auth capacity g records -∗ frag capacity g i old ==∗
      auth capacity g (PartialMap.insert (M := RecordMap) records i new) ∗ frag capacity g i new) :=
    ghost_map_update (H := RecordMap) (GF := GF) new
  iapply law $$ Ha Hf

end MachCSL.Logic.FsInodeRegion
