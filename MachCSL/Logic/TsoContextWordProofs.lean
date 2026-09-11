import MachCSL.Logic.TsoContextWordSpec
import MachCSL.Logic.TsoContextStoreProofs

namespace MachCSL.Logic.TsoContextWord
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContext
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance pointsto_timeless names ξ a dq word :
    Timeless (pointsto capacity names ξ a dq word) := by
  unfold pointsto
  infer_instance

theorem pointsto_map names ξ a word :
    iprop(pointsto capacity names ξ a (.own 1) word ⊣⊢
      ⌜Aligned a⌝ ∗ TsoContextStore.physMap capacity names ξ (TsoStore.windowMap a 8 word)) := by
  unfold pointsto TsoContextStore.physMap
  rw [(TsoStore.window_map (fun b byte => physPointsto capacity names ξ b (.own 1) byte)
    a 8 word (by decide)).to_eq]
  exact .rfl

theorem aligned names ξ a dq word :
    iprop(pointsto capacity names ξ a dq word ⊢ ⌜Aligned a⌝) := by
  unfold pointsto
  iintro ⟨%h, _⟩
  ipureintro
  exact h

/-- The actual native heap camera gives word agreement without an authority premise. -/
theorem agree names ξ ξ' a dq dq' left right :
    iprop(⊢ pointsto capacity names ξ a dq left -∗
      pointsto capacity names ξ' a dq' right -∗ ⌜left = right⌝) := by
  iintro Hl Hr
  ihave %bytes : ⌜∀ j, j < 8 → nthByte left j = nthByte right j⌝ $$ [Hl Hr]
  · iapply pure_forall.mpr
    iintro %j
    iapply pure_imp.mpr
    iintro %hj
    unfold pointsto
    icases Hl with ⟨_, Hl⟩
    icases Hr with ⟨_, Hr⟩
    have lookup : (List.range 8)[j]? = some j := by simp [hj]
    ihave Hl := BigSepL.bigSepL_lookup lookup $$ Hl
    ihave Hr := BigSepL.bigSepL_lookup lookup $$ Hr
    unfold physPointsto
    icases Hl with ⟨%t, Hl, _⟩
    icases Hr with ⟨%t', Hr, _⟩
    iapply Tso.physBytePointsto_agree capacity.heap.ledger names.tso.ledger.bytes
      (addressAdd a j) dq dq' (nthByte left j) (nthByte right j) $$ [$Hl $Hr]
  · ipureintro
    exact bv_eq_of_bytes left right bytes

/-- All eight byte predictions use the same arbitrary allowed view. -/
theorem load_fact names cpu ξ eraImage g a dq word :
    iprop(⊢ heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      ownContext capacity names cpu ξ -∗ pointsto capacity names ξ a dq word -∗
      ⌜Readback g cpu a word⌝) := by
  iintro Hheap Htso Hrun Hword
  ihave %bytes : ⌜∀ j, j < 8 → ∀ view, g.views cpu ≤ view →
      read g.image g.log (hartAgent cpu) view (addressAdd a j) = some (nthByte word j)⌝
      $$ [Hheap Htso Hrun Hword]
  · iapply pure_forall.mpr
    iintro %j
    iapply pure_imp.mpr
    iintro %hj
    unfold pointsto
    icases Hword with ⟨_, Hbytes⟩
    have lookup : (List.range 8)[j]? = some j := by simp [hj]
    ihave Hb := BigSepL.bigSepL_lookup lookup $$ Hbytes
    iapply TsoContext.load_fact capacity names cpu ξ eraImage g _ dq _ $$ Hheap Htso Hrun Hb
  · ipureintro
    intro view allowed
    have h : ReadsBytes g.image g.log (hartAgent cpu) view a 8 word :=
      fun j hj => bytes j hj view allowed
    exact ⟨h, readBytes_of_bytes _ a 8 word h⟩

theorem load names cpu ξ eraImage g a dq word :
    iprop(⊢ heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      ownContext capacity names cpu ξ -∗ pointsto capacity names ξ a dq word -∗
      heapAt capacity names g ∗ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      ownContext capacity names cpu ξ ∗ pointsto capacity names ξ a dq word ∗
      ⌜Readback g cpu a word⌝) := by
  iintro Hheap Htso Hrun Hword
  ihave %reads := load_fact capacity names cpu ξ eraImage g a dq word $$ Hheap Htso Hrun Hword
  iframe Hheap Htso Hrun Hword
  ipureintro
  exact reads

theorem ordinary names cpu ξ eraImage before after a old new
    (step : TsoContextStore.OrdinaryTransition before after (TsoStore.windowMap a 8 new) cpu) :
    iprop(⊢ heapAt capacity names before -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      ownContext capacity names cpu ξ -∗ pointsto capacity names ξ a (.own 1) old ==∗
      heapAt capacity names after ∗ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      ownContext capacity names cpu ξ ∗ pointsto capacity names ξ a (.own 1) new ∗
      ⌜Readback after cpu a new⌝) := by
  rw [(pointsto_map capacity names ξ a old).to_eq]
  iintro Hheap Htso Hrun ⟨%aligned, Hold⟩
  imod TsoContextStore.ordinary capacity names cpu ξ eraImage before after
    (TsoStore.windowMap a 8 old) (TsoStore.windowMap a 8 new)
    (TsoStore.windowMap_sameDomain a 8 old new) step $$ Hheap Htso Hrun Hold
    with ⟨Hheap, Htso, Hrun, Hnew⟩
  imodintro
  ihave Hword : pointsto capacity names ξ a (.own 1) new $$ [Hnew]
  · rw [(pointsto_map capacity names ξ a new).to_eq]
    iframe Hnew
    ipureintro
    exact aligned
  iapply load capacity names cpu ξ eraImage after a (.own 1) new $$ Hheap Htso Hrun Hword

theorem actual : Spec capacity where
  load := load capacity
  ordinary := ordinary capacity

end MachCSL.Logic.TsoContextWord
