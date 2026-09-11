import MachCSL.Logic.TsoContextSpec
import MachCSL.Logic.TsoInterpProofs
import MachCSL.Logic.HeapProofs

namespace MachCSL.Logic.TsoContext
open Iris Iris.BI MachCSL.Memory MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance ctxAt_timeless ξ q B D : Timeless (ctxAt capacity ξ q B D) := by
  unfold ctxAt
  infer_instance
instance ownContext_timeless names cpu ξ : Timeless (ownContext capacity names cpu ξ) := by
  unfold ownContext
  infer_instance
instance floor_persistent ξ B : Persistent (floor capacity ξ B) := by
  unfold floor
  infer_instance
instance floor_timeless ξ B : Timeless (floor capacity ξ B) := by
  unfold floor
  infer_instance
instance physPointsto_timeless names ξ a dq byte :
    Timeless (physPointsto capacity names ξ a dq byte) := by
  unfold physPointsto
  infer_instance

theorem floor_zero ξ : iprop(⊢ floor capacity ξ 0) :=
  Tso.Views.llb_zero capacity.views ξ.bound

theorem floor_le ξ B smaller (le : smaller ≤ B) :
    iprop(⊢ floor capacity ξ B -∗ floor capacity ξ smaller) :=
  Tso.Views.llb_le capacity.views ξ.bound B smaller le

theorem ctxAt_agree ξ q q' B D B' D' :
    iprop(⊢ ctxAt capacity ξ q B D -∗ ctxAt capacity ξ q' B' D' -∗ ⌜B = B' ∧ D = D'⌝) := by
  unfold ctxAt
  iintro ⟨Hb, Hd⟩ ⟨Hb', Hd'⟩
  letI := capacity.views.monoNat ξ.bound
  ihave %hb := MonoNat.auth_own_agree ξ.bound (.own q) (.own q') (.ofNat B) (.ofNat B') $$ Hb Hb'
  ihave %hd := Tso.History.dset_agree capacity.history ξ.dirty q q' D D' $$ Hd Hd'
  ipureintro
  exact ⟨congrArg MaxNat.toNat hb.2, hd⟩

theorem ctxAt_halves ξ B D :
    iprop(ctxAt capacity ξ 1 B D ⊣⊢
      ctxAt capacity ξ (Qp.half 1) B D ∗ ctxAt capacity ξ (Qp.half 1) B D) := by
  unfold ctxAt
  letI := capacity.views.monoNat ξ.bound
  have h := (inferInstance : Fractional (fun q => Tso.Views.natAuth capacity.views ξ.bound (.own q) B)).fractional
    (Qp.half 1) (Qp.half 1)
  simp only [Qp.half_add_half] at h
  rw [h.to_eq, (Tso.History.dset_halves capacity.history ξ.dirty D).to_eq]
  isplit
  · iintro ⟨⟨Hb, Hb'⟩, ⟨Hd, Hd'⟩⟩
    iframe Hb Hd Hb' Hd'
  · iintro ⟨⟨Hb, Hd⟩, ⟨Hb', Hd'⟩⟩
    iframe Hb Hb' Hd Hd'

/-- Source `own_context_floor_view`; the existing context view receipt is
returned with its bound, without advancing the actual view. -/
theorem ownContext_floor_view names cpu ξ lower :
    iprop(⊢ ownContext capacity names cpu ξ -∗ floor capacity ξ lower -∗
      ownContext capacity names cpu ξ ∗ ∃ K : Nat,
        Tso.Views.viewLB capacity.views names.tso.views names.tso.logLength (hartAgent cpu) K ∗
        ⌜lower ≤ K⌝) := by
  unfold ownContext ctxAt floor
  iintro ⟨%B, %K, %W, %D, ⟨Hb, Hd⟩, #Hview, %bound, #HW, %watermark, #Hoks⟩ Hfloor
  ihave %le := Tso.Views.llb_valid capacity.views ξ.bound (.own 1) B lower $$ Hb Hfloor
  isplitl [Hb Hd]
  · iexists B, K, W, D
    iframe Hb Hd Hview HW Hoks
    ipureintro
    exact ⟨bound, watermark⟩
  · iexists K
    iframe Hview
    ipureintro
    omega

/-- The same running context cannot be owned on two harts, even distinct ones. -/
theorem ownContext_exclusive names cpu other ξ :
    iprop(⊢ ownContext capacity names cpu ξ -∗ ownContext capacity names other ξ -∗ False) := by
  unfold ownContext ctxAt
  iintro ⟨%B, %K, %W, %D, ⟨Hb, _⟩, _⟩ ⟨%B', %K', %W', %D', ⟨Hb', _⟩, _⟩
  letI := capacity.views.monoNat ξ.bound
  iapply MonoNat.auth_own_exclusive ξ.bound (.ofNat B) (.ofNat B') $$ Hb Hb'

/-- Boot allocation requires no assumed positive view or log position. -/
theorem allocate (names : Names) (cpu : CPU) :
    iprop(⊢ |==> ∃ ξ, ownContext capacity names cpu ξ) := by
  imod Tso.Views.natAuth_alloc capacity.views 0 with ⟨%bound, Hb, _⟩
  imod Tso.History.dset_alloc capacity.history with ⟨%dirty, Hd⟩
  imodintro
  iexists (CtxId.mk bound dirty)
  unfold ownContext ctxAt
  iexists 0, 0, 0, (∅ : Tso.History.DirtySet)
  iframe Hb Hd
  ihave Hv := Tso.Views.viewLB_zero capacity.views names.tso.views names.tso.logLength (hartAgent cpu)
  ihave Hw := Tso.Views.llb_zero capacity.views names.tso.logLength
  iframe Hv Hw
  isplit
  · ipureintro; omega
  isplit
  · ipureintro; simp
  exact BigSepS.bigSepS_empty_intro

/-- Physical form of `ctx_load_ok`: clean and authored dirty bytes both predict
all allowed ordinary read views. No state update or view advance occurs. -/
theorem load_fact names cpu ξ eraImage g a dq byte :
    iprop(⊢ heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      ownContext capacity names cpu ξ -∗ physPointsto capacity names ξ a dq byte -∗
      ⌜∀ view, g.views cpu ≤ view → read g.image g.log (hartAgent cpu) view a = some byte⌝) := by
  unfold heapAt ownContext ctxAt physPointsto floor
  iintro ⟨%memory, Hheap, %decoded⟩ Htso
    ⟨%B, %K, %W, %D, ⟨Hb, Hd⟩, Hview, %bound, _HW, %_watermark, Hoks⟩
    ⟨%time, ⟨Hbyte, _⟩, Htime, Hbit⟩
  have heapValid := Heap.valid capacity.heap names.heap memory a dq byte
  rw [Heap.pointsto_eq_byteElem] at heapValid
  ihave %lookup := heapValid $$ Hheap Hbyte
  ihave %valid := Tso.Interp.tsoInterpAt_timestamp_valid capacity.tso names.tso eraImage g a dq
    (time, Tso.payNone) $$ Htso Htime
  obtain ⟨actual, value, latest⟩ := Tso.timestampOK_latest valid
  have equal : actual = byte := by
    have stored : g.memory a = some byte := by rw [← decoded]; exact lookup
    exact Option.some.inj (value.symm.trans stored)
  subst actual
  unfold Tso.Interp.tsoInterpAt
  icases Htso with ⟨%_timestamps, %entries, _, _, _, Hlog, %rep, _, Hv, _⟩
  have viewValid := Tso.Views.viewAuth_valid capacity.views names.tso.views names.tso.logLength
    (Tso.Interp.avf g) (hartAgent cpu) K
  rw [Tso.Interp.avf_hart] at viewValid
  ihave %viewBound := viewValid $$ Hv Hview
  icases Hbit with (Hclean | Hdirty)
  · ihave %timeBound := Tso.Views.llb_valid capacity.views ξ.bound (.own 1) B time $$ Hb Hclean
    ipureintro
    intro view above
    exact read_of_latest g.image g.log (hartAgent cpu) view a time byte latest
      (visible_below _ _ _ _ (by omega))
  · ihave %member := Tso.History.dset_lookup capacity.history ξ.dirty 1 D (time, a) $$ Hd Hdirty
    ihave Hok := BigSepS.bigSepS_elem_of member $$ Hoks
    iapply pure_forall.mpr
    iintro %view
    iapply pure_imp.mpr
    iintro %above
    ihave %visible := Tso.History.dirtyOK_visible capacity.history names.tso.logEntries entries g.log
      (hartAgent cpu) B (time, a) view rep (by omega) $$ Hlog Hok
    ipureintro
    exact read_of_latest g.image g.log (hartAgent cpu) view a time byte latest visible

/-- The source gate preserves the complete heap metadata and both context arms. -/
theorem load names cpu ξ eraImage g a dq byte :
    iprop(⊢ heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      ownContext capacity names cpu ξ -∗ physPointsto capacity names ξ a dq byte -∗
      heapAt capacity names g ∗ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      ownContext capacity names cpu ξ ∗ physPointsto capacity names ξ a dq byte ∗
      ⌜∀ view, g.views cpu ≤ view → read g.image g.log (hartAgent cpu) view a = some byte⌝) := by
  iintro Hheap Htso Hrun Hbyte
  ihave %reads := load_fact capacity names cpu ξ eraImage g a dq byte $$ Hheap Htso Hrun Hbyte
  iframe Hheap Htso Hrun Hbyte
  ipureintro
  exact reads

theorem actual : TsoContextSpec capacity where
  allocate := allocate capacity
  load := load capacity

end MachCSL.Logic.TsoContext
