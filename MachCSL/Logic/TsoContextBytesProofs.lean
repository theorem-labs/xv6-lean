import MachCSL.Logic.TsoContextBytesSpec
import MachCSL.Logic.TsoContextProofs
import MachCSL.Logic.TsoReadProofs

namespace MachCSL.Logic.TsoContextBytes
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContext
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance window_timeless names ξ a n dq word :
    Timeless (window capacity names ξ a n dq word) := by
  unfold window
  infer_instance

/-- The actual native heap camera gives word agreement without an authority premise. -/
theorem agree names ξ ξ' a n dq dq' (left right : BitVec (8 * n)) :
    iprop(⊢ window capacity names ξ a n dq left -∗
      window capacity names ξ' a n dq' right -∗ ⌜left = right⌝) := by
  iintro Hl Hr
  ihave %bytes : ⌜∀ j, j < n → nthByte left j = nthByte right j⌝ $$ [Hl Hr]
  · iapply pure_forall.mpr
    iintro %j
    iapply pure_imp.mpr
    iintro %hj
    unfold window
    have lookup : (List.range n)[j]? = some j := by simp [hj]
    ihave Hl := BigSepL.bigSepL_lookup lookup $$ Hl
    ihave Hr := BigSepL.bigSepL_lookup lookup $$ Hr
    unfold physPointsto
    icases Hl with ⟨%t, Hl, _⟩
    icases Hr with ⟨%t', Hr, _⟩
    iapply Tso.physBytePointsto_agree capacity.heap.ledger names.tso.ledger.bytes
      (addressAdd a j) dq dq' (nthByte left j) (nthByte right j) $$ [$Hl $Hr]
  · ipureintro
    exact bv_eq_of_bytes left right bytes

/-- All byte predictions use the same arbitrary allowed view. -/
theorem load_fact names cpu ξ eraImage g a n dq word :
    iprop(⊢ heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      ownContext capacity names cpu ξ -∗ window capacity names ξ a n dq word -∗
      ⌜Readback g cpu a n word⌝) := by
  iintro Hheap Htso Hrun Hword
  ihave %bytes : ⌜∀ j, j < n → ∀ view, g.views cpu ≤ view →
      read g.image g.log (hartAgent cpu) view (addressAdd a j) = some (nthByte word j)⌝
      $$ [Hheap Htso Hrun Hword]
  · iapply pure_forall.mpr
    iintro %j
    iapply pure_imp.mpr
    iintro %hj
    unfold window
    have lookup : (List.range n)[j]? = some j := by simp [hj]
    ihave Hb := BigSepL.bigSepL_lookup lookup $$ Hword
    iapply TsoContext.load_fact capacity names cpu ξ eraImage g _ dq _ $$ Hheap Htso Hrun Hb
  · ipureintro
    intro view allowed
    have h : ReadsBytes g.image g.log (hartAgent cpu) view a n word :=
      fun j hj => bytes j hj view allowed
    exact ⟨h, readBytes_of_bytes _ a n word h⟩

theorem load names cpu ξ eraImage g a n dq word :
    iprop(⊢ heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      ownContext capacity names cpu ξ -∗ window capacity names ξ a n dq word -∗
      heapAt capacity names g ∗ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      ownContext capacity names cpu ξ ∗ window capacity names ξ a n dq word ∗
      ⌜Readback g cpu a n word⌝) := by
  iintro Hheap Htso Hrun Hword
  ihave %reads := load_fact capacity names cpu ξ eraImage g a n dq word $$ Hheap Htso Hrun Hword
  iframe Hheap Htso Hrun Hword
  ipureintro
  exact reads


instance byte_discard_persistent names ξ a byte :
    Persistent (physPointsto capacity names ξ a .discard byte) := by
  letI := capacity.heap.ledger.bytes
  letI := capacity.heap.ledger.timestamps
  unfold physPointsto
  infer_instance

instance window_discard_persistent names ξ a n word :
    Persistent (window capacity names ξ a n .discard word) := by
  unfold window
  infer_instance

theorem byte_split names ξ a byte (q1 q2 : Qp) :
    iprop(physPointsto capacity names ξ a (.own (q1 + q2)) byte ⊢
      physPointsto capacity names ξ a (.own q1) byte ∗
      physPointsto capacity names ξ a (.own q2) byte) := by
  letI := capacity.heap.ledger.timestamps
  unfold physPointsto
  iintro ⟨%time, Hb, Ht, #Hseen⟩
  ihave ⟨Hb1, Hb2⟩ := (Fractional.fractional
    (Φ := fun q => Tso.physBytePointsto capacity.heap.ledger names.tso.ledger.bytes a (.own q) byte)
    q1 q2).mp $$ Hb
  ihave ⟨Ht1, Ht2⟩ := (Fractional.fractional
    (Φ := fun q => Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps (.own q) a
      (time, Tso.payNone)) q1 q2).mp $$ Ht
  isplitl [Hb1 Ht1]
  · iexists time; iframe Hb1 Ht1 Hseen
  · iexists time; iframe Hb2 Ht2 Hseen

theorem window_split names ξ a n word (q1 q2 : Qp) :
    iprop(window capacity names ξ a n (.own (q1 + q2)) word ⊢
      window capacity names ξ a n (.own q1) word ∗ window capacity names ξ a n (.own q2) word) := by
  unfold window
  rw [← BigSepL.bigSepL_sep_eqv.to_eq]
  exact BigSepL.bigSepL_mono fun {_ _} _ => byte_split capacity names ξ _ _ q1 q2

theorem byte_persist names ξ a dq byte :
    iprop(physPointsto capacity names ξ a dq byte ⊢ |==> physPointsto capacity names ξ a .discard byte) := by
  unfold physPointsto Tso.physBytePointsto
  iintro ⟨%time, ⟨Hb, %ram⟩, Ht, Hseen⟩
  letI := capacity.heap.ledger.bytes
  imod ghost_map_elem_persist (GF := GF) (K := PhysicalAddress) (V := Byte) (H := Tso.AddressMap)
    names.tso.ledger.bytes a dq byte $$ Hb with Hb
  letI := capacity.heap.ledger.timestamps
  imod ghost_map_elem_persist (GF := GF) (K := PhysicalAddress) (V := Tso.TimestampElem) (H := Tso.AddressMap)
    names.tso.ledger.timestamps a dq (time, Tso.payNone) $$ Ht with Ht
  imodintro
  iexists time
  iframe Hb Ht Hseen
  ipureintro; exact ram

theorem window_persist names ξ a n dq word :
    iprop(window capacity names ξ a n dq word ⊢ |==> window capacity names ξ a n .discard word) := by
  unfold window
  iintro H
  iapply BigSepL.bigSepL_bupd
  iapply BigSepL.bigSepL_mono $$ H
  intro _ _ _
  exact byte_persist capacity names ξ _ dq _

/-- Matching timestamp-zero fractions yield actual clean context bytes. -/
theorem zero_byte names ξ a dq byte :
    iprop(Tso.physBytePointsto capacity.heap.ledger names.tso.ledger.bytes a dq byte ∗
      Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps dq a (0, Tso.payNone) ⊢
      physPointsto capacity names ξ a dq byte) := by
  iintro ⟨Hb, Ht⟩
  unfold physPointsto
  iexists 0
  iframe Hb Ht
  ileft
  exact TsoContext.floor_zero capacity ξ

/-- Existing full timestamp-zero clients are consumed, never reallocated. -/
theorem of_stored_zero names ξ a n word :
    iprop(TsoStore.storedWindow capacity names a n word 0 ⊢
      window capacity names ξ a n (.own 1) word) := by
  unfold TsoStore.storedWindow TsoStore.storedByte window
  exact BigSepL.bigSepL_mono fun {_ _} _ => zero_byte capacity names ξ _ (.own 1) _

/-- Discarded byte clients and pristine discarded timestamps match exactly.
This does not promote discarded timestamps to a requested owned fraction. -/
theorem of_pristine_discard names ξ a n word :
    iprop(TsoRead.byteWindow capacity.heap.ledger names.tso.ledger.bytes a n .discard word ∗
      TsoRead.pristineWindow capacity.heap.ledger names.tso.ledger.timestamps a n ⊢
      window capacity names ξ a n .discard word) := by
  unfold TsoRead.byteWindow TsoRead.pristineWindow TsoRead.pristineByte window
  rw [← BigSepL.bigSepL_sep_eqv.to_eq]
  exact BigSepL.bigSepL_mono fun {_ _} _ => zero_byte capacity names ξ _ .discard _

/-- Exact sublist extraction and linear reassembly; overlapping windows must
be opened in sequence or use legitimate discarded ownership. -/
theorem slice_acc names ξ a n dq word (lo len : Nat) :
    iprop(window capacity names ξ a n dq word ⊢
      ([∗list] j ∈ ((List.range n).drop lo).take len,
        physPointsto capacity names ξ (addressAdd a j) dq (nthByte word j)) ∗
      (([∗list] j ∈ ((List.range n).drop lo).take len,
        physPointsto capacity names ξ (addressAdd a j) dq (nthByte word j)) -∗
       window capacity names ξ a n dq word)) := by
  unfold window
  iintro H
  ihave ⟨Hprefix, Hrest⟩ := (BigSepL.bigSepL_take_drop (n := lo)).mp $$ H
  ihave ⟨Hslice, Hsuffix⟩ := (BigSepL.bigSepL_take_drop (n := len)).mp $$ Hrest
  iframe Hslice
  iintro Hslice
  iapply (BigSepL.bigSepL_take_drop (n := lo)).mpr
  iframe Hprefix
  iapply (BigSepL.bigSepL_take_drop (n := len)).mpr
  iframe Hslice Hsuffix

/-- Reindex the selected contiguous interval without changing its bytes. -/
theorem slice_eq_window names ξ a n dq (word : BitVec (8 * n)) (lo len : Nat)
    (small : BitVec (8 * len)) (bound : lo + len ≤ n)
    (bytes : ∀ j, j < len → nthByte word (lo + j) = nthByte small j) :
    iprop([∗list] j ∈ ((List.range n).drop lo).take len,
      physPointsto capacity names ξ (addressAdd a j) dq (nthByte word j)) =
    window capacity names ξ (addressAdd a lo) len dq small := by
  have indices : ((List.range n).drop lo).take len = (List.range len).map (lo + ·) := by
    rw [List.range_eq_range', List.drop_range']
    simp only [Nat.mul_one, Nat.zero_add]
    rw [List.take_range'_of_length_ge (by omega), List.range_eq_range', List.map_add_range']
    simp
  rw [indices, BigSepL.bigSepL_map]
  unfold window
  apply BigSepL.bigSepL_eq
  intro k j lookup
  have inside : j < len := List.mem_range.mp (List.mem_of_getElem? lookup)
  have addr : addressAdd a (lo + j) = addressAdd (addressAdd a lo) j := by
    simp only [addressAdd, BitVec.ofNat_add, BitVec.add_assoc]
  rw [addr, bytes j inside]

theorem subwindow_acc names ξ a n dq (word : BitVec (8 * n)) (lo len : Nat)
    (small : BitVec (8 * len)) (bound : lo + len ≤ n)
    (bytes : ∀ j, j < len → nthByte word (lo + j) = nthByte small j) :
    iprop(window capacity names ξ a n dq word ⊢
      window capacity names ξ (addressAdd a lo) len dq small ∗
      (window capacity names ξ (addressAdd a lo) len dq small -∗
       window capacity names ξ a n dq word)) := by
  have rule := slice_acc capacity names ξ a n dq word lo len
  rw [slice_eq_window capacity names ξ a n dq word lo len small bound bytes] at rule
  exact rule

theorem actual : Spec capacity := ⟨load capacity⟩

end MachCSL.Logic.TsoContextBytes
