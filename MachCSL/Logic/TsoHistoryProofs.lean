import MachCSL.Logic.TsoHistorySpec

/-! Native Iris proofs of `TsoGhost.v` dirty-set and dirty-entry laws. -/
namespace MachCSL.Logic.Tso.History
open MachCSL.Memory Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI Auth
open Iris.Std.LawfulSet Iris.Std.PartialMap Iris.Std.LawfulPartialMap
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance dsetIn_persistent γ k : Persistent (dsetIn capacity γ k) := by
  unfold dsetIn; infer_instance
instance dsetIn_timeless γ k : Timeless (dsetIn capacity γ k) := by
  unfold dsetIn; infer_instance
instance dsetAuth_timeless γ q s : Timeless (dsetAuth capacity γ q s) := by
  unfold dsetAuth; infer_instance
instance logElem_persistent γ i m : Persistent (logElem capacity γ i m) := by
  letI := capacity.logs
  unfold logElem; infer_instance
instance logElem_timeless γ i m : Timeless (logElem capacity γ i m) := by
  letI := capacity.logs
  unfold logElem; infer_instance
instance logAuth_timeless γ dq m : Timeless (logAuth capacity γ dq m) := by
  letI := capacity.logs
  unfold logAuth; infer_instance
instance dirtyOK_persistent γ h bound key : Persistent (dirtyOK capacity γ h bound key) := by
  unfold dirtyOK; infer_instance
instance dirtyOK_timeless γ h bound key : Timeless (dirtyOK capacity γ h bound key) := by
  unfold dirtyOK; infer_instance

theorem dset_alloc : iprop(⊢ |==> ∃ γ, dsetAuth capacity γ 1 ∅) := by
  unfold dsetAuth
  apply iOwn_alloc (E := capacity.dirty)
  exact Auth.auth_valid.mpr trivial

instance dsetAuth_fractional γ s : Fractional (fun q => dsetAuth capacity γ q s) where
  fractional p q := by
    unfold dsetAuth
    rw [← (iOwn_op (E := capacity.dirty)).to_eq, ← Auth.auth_dfrac_op, DFrac.op_own]
    exact .rfl

theorem dset_halves γ s :
    iprop(dsetAuth capacity γ 1 s ⊣⊢
      dsetAuth capacity γ (Qp.half 1) s ∗ dsetAuth capacity γ (Qp.half 1) s) := by
  have h := (dsetAuth_fractional capacity γ s).fractional (Qp.half 1) (Qp.half 1)
  simpa only [Qp.half_add_half] using h

theorem dset_agree γ q1 q2 s1 s2 :
    iprop(⊢ dsetAuth capacity γ q1 s1 -∗ dsetAuth capacity γ q2 s2 -∗ ⌜s1 = s2⌝) := by
  unfold dsetAuth
  iintro H1 H2
  icases (iOwn_cmraValid_op (E := capacity.dirty)) $$ [$H1 $H2] with %hv
  ipureintro
  exact LeibnizSet.valid.inj (Auth.auth_dfrac_op_inv hv)

theorem dset_lookup γ q s k :
    iprop(⊢ dsetAuth capacity γ q s -∗ dsetIn capacity γ k -∗ ⌜k ∈ s⌝) := by
  unfold dsetAuth dsetIn
  iintro Ha Hk
  icases (iOwn_cmraValid_op (E := capacity.dirty)) $$ [$Ha $Hk] with %hv
  ipureintro
  have hi := (Auth.both_dfrac_valid_discrete.mp hv).2.1
  exact (LeibnizSet.included_iff_subset _ _).mp hi k (mem_singleton.mpr rfl)

/-- Membership is remintable even while another owner retains the same receipt. -/
theorem dset_get γ q s k (member : k ∈ s) :
    iprop(⊢ dsetAuth capacity γ q s ==∗ dsetAuth capacity γ q s ∗ dsetIn capacity γ k) := by
  unfold dsetAuth dsetIn
  iintro H
  rw [← (iOwn_op (E := capacity.dirty)).to_eq]
  iapply (iOwn_update (E := capacity.dirty)) $$ H
  apply Auth.auth_update_dfrac_alloc
  apply (LeibnizSet.included_iff_subset _ _).mpr
  intro key hk
  obtain rfl := mem_singleton.mp hk
  exact member

theorem dset_insert γ s k :
    iprop(⊢ dsetAuth capacity γ 1 s ==∗
      dsetAuth capacity γ 1 (s ∪ {k}) ∗ dsetIn capacity γ k) := by
  iintro H
  ihave >H' : |==> dsetAuth capacity γ 1 (s ∪ {k}) $$ [H]
  · unfold dsetAuth
    iapply (iOwn_update (E := capacity.dirty)) $$ H
    exact Auth.auth_update_auth (LeibnizSet.localUpdate s ∅ (s ∪ {k}) union_subset_left)
  · iapply dset_get capacity γ 1 (s ∪ {k}) k (mem_union.mpr (.inr (mem_singleton.mpr rfl))) $$ H'

theorem dirtyOK_mono γ h bound bound' k (le : bound ≤ bound') :
    iprop(⊢ dirtyOK capacity γ h bound k -∗ dirtyOK capacity γ h bound' k) := by
  unfold dirtyOK
  iintro H
  icases H with (%hb | H)
  · ileft
    ipureintro
    omega
  · iright
    iexact H

theorem dirtyOK_clean γ h bound k (le : k.1 ≤ bound) :
    iprop(⊢ dirtyOK capacity γ h bound k) := by
  unfold dirtyOK
  ileft
  ipureintro
  exact le

theorem dirtyOK_author γ h bound k i m (timestamp : k.1 = i + 1) (author : m.author = h) :
    iprop(⊢ logElem capacity γ i m -∗ dirtyOK capacity γ h bound k) := by
  unfold dirtyOK
  iintro H
  iright
  iexists i, m
  iframe H
  ipureintro
  exact ⟨timestamp, author⟩

theorem log_alloc : iprop(⊢ |==> ∃ γ, logAuth capacity γ (.own 1) ∅) := by
  letI := capacity.logs
  exact ghost_map_alloc_empty

theorem log_agree γ dq1 dq2 map1 map2 :
    iprop(⊢ logAuth capacity γ dq1 map1 -∗ logAuth capacity γ dq2 map2 -∗ ⌜map1 = map2⌝) := by
  letI := capacity.logs
  exact ghost_map_auth_agree γ dq1 dq2 map1 map2

instance logAuth_fractional γ m : Fractional (fun q => logAuth capacity γ (.own q) m) := by
  letI := capacity.logs
  unfold logAuth
  infer_instance

theorem log_halves γ m :
    iprop(logAuth capacity γ (.own 1) m ⊣⊢
      logAuth capacity γ (.own (Qp.half 1)) m ∗ logAuth capacity γ (.own (Qp.half 1)) m) := by
  have h := (logAuth_fractional capacity γ m).fractional (Qp.half 1) (Qp.half 1)
  simpa only [Qp.half_add_half] using h

theorem log_lookup γ dq entries i m :
    iprop(⊢ logAuth capacity γ dq entries -∗ logElem capacity γ i m -∗
      ⌜get? entries i = some m⌝) := by
  letI := capacity.logs
  exact ghost_map_lookup

theorem log_elem_agree γ i m1 m2 :
    iprop(logElem capacity γ i m1 ∗ logElem capacity γ i m2 ⊢ ⌜m1 = m2⌝) := by
  letI := capacity.logs
  exact ghost_map_elem_agree γ i .discard .discard m1 m2

/-- Fresh entries immediately yield persistent receipts, as at source log append. -/
theorem log_insert γ entries i m (fresh : get? entries i = none) :
    iprop(⊢ logAuth capacity γ (.own 1) entries ==∗
      logAuth capacity γ (.own 1) (insert entries i m) ∗ logElem capacity γ i m) := by
  letI := capacity.logs
  exact ghost_map_insert_persist i m fresh

theorem logRep_empty : LogRep ∅ [] := by
  intro i
  simp [get?_empty]

theorem logRep_fresh {entries : LogMap (Message 64)} {log : WriteLog 64}
    (rep : LogRep entries log) : get? entries log.length = none := by
  rw [rep]
  simp

theorem logRep_append {entries : LogMap (Message 64)} {log : WriteLog 64}
    (rep : LogRep entries log) (m : Message 64) :
    LogRep (insert entries log.length m) (log ++ [m]) := by
  intro i
  rw [get?_insert]
  by_cases eq : log.length = i
  · subst i
    simp
  · simp only [eq, ↓reduceIte]
    rw [rep i]
    by_cases lt : i < log.length
    · simp [List.getElem?_append, lt]
    · have gt : log.length < i := by omega
      have h₁ : log[i]? = none := List.getElem?_eq_none (by omega)
      have h₂ : (log ++ [m])[i]? = none := List.getElem?_eq_none (by simp; omega)
      rw [h₁, h₂]

/-- Append at the exact next zero-indexed log position and retain any Iris frame. -/
theorem log_append_frame γ entries log m (rep : LogRep entries log) (P : IProp GF) :
    iprop(⊢ logAuth capacity γ (.own 1) entries ∗ P ==∗
      logAuth capacity γ (.own 1) (insert entries log.length m) ∗
      logElem capacity γ log.length m ∗ P ∗
      ⌜LogRep (insert entries log.length m) (log ++ [m])⌝) := by
  iintro ⟨Ha, HP⟩
  imod log_insert capacity γ entries log.length m (logRep_fresh rep) $$ Ha with ⟨Ha, Hm⟩
  imodintro
  iframe Ha Hm HP
  ipureintro
  exact logRep_append rep m

/-- An existing persistent receipt agrees with the represented list. -/
theorem log_lookup_list γ dq entries log i m (rep : LogRep entries log) :
    iprop(⊢ logAuth capacity γ dq entries -∗ logElem capacity γ i m -∗
      ⌜log[i]? = some m⌝) := by
  iintro Ha Hm
  ihave %lookup := log_lookup capacity γ dq entries i m $$ Ha Hm
  ipureintro
  rw [← rep]
  exact lookup

/-- The source author's dirty justification entails the actual visibility arm. -/
theorem dirtyOK_visible γ entries log h bound key view
    (rep : LogRep entries log) (le : bound ≤ view) :
    iprop(⊢ logAuth capacity γ (.own 1) entries -∗ dirtyOK capacity γ h bound key -∗
      ⌜visible h view log key.1 = true⌝) := by
  unfold dirtyOK
  iintro Ha H
  icases H with (%hb | ⟨%i, %m, %ht, Hm, %author⟩)
  · ipureintro
    simp [visible, show key.1 ≤ view by omega]
  · ihave %lookup := log_lookup_list capacity γ (.own 1) entries log i m rep $$ Ha Hm
    ipureintro
    simp [visible, ht, lookup, author]

theorem dset_valid γ q set :
    iprop(⊢ dsetAuth capacity γ q set -∗ ⌜✓ DFrac.own q⌝) := by
  unfold dsetAuth
  iintro H
  icases (iOwn_cmraValid (E := capacity.dirty)) $$ H with %hv
  ipureintro
  exact (Auth.auth_dfrac_valid.mp hv).1

theorem log_valid γ dq entries :
    iprop(⊢ logAuth capacity γ dq entries -∗ ⌜✓ dq⌝) := by
  letI := capacity.logs
  exact ghost_map_auth_valid γ dq entries

/-- No hypothesis of absence is required when inserting an already registered key. -/
theorem dset_insert_frame γ s k (P : IProp GF) :
    iprop(⊢ dsetAuth capacity γ 1 s ∗ P ==∗
      dsetAuth capacity γ 1 (s ∪ {k}) ∗ dsetIn capacity γ k ∗ P) := by
  iintro ⟨Ha, HP⟩
  imod dset_insert capacity γ s k $$ Ha with ⟨Ha, Hk⟩
  imodintro
  iframe Ha Hk HP

/-- The list-map representation condition is inhabited for every actual log. -/
theorem logRep_exists (log : WriteLog 64) : ∃ entries, LogRep entries log := by
  have aux : ∀ rev : WriteLog 64, ∃ entries, LogRep entries rev.reverse := by
    intro rev
    induction rev with
    | nil => exact ⟨∅, logRep_empty⟩
    | cons m rest ih =>
      obtain ⟨entries, rep⟩ := ih
      exact ⟨insert entries rest.reverse.length m, by simpa using logRep_append rep m⟩
  simpa using aux log.reverse

/-- Implementation of the independently importable resource contract. -/
theorem historySpec : HistorySpec capacity where
  dirtyAlloc := dset_alloc capacity
  dirtyHalves := dset_halves capacity
  dirtyAgree := dset_agree capacity
  dirtyLookup := dset_lookup capacity
  dirtyGet := dset_get capacity
  dirtyInsert := dset_insert capacity
  dirtyMono := dirtyOK_mono capacity
  logAlloc := log_alloc capacity
  logAgree := log_agree capacity
  logLookup := log_lookup capacity
  logInsert := log_insert capacity
  logAppend := log_append_frame capacity

end MachCSL.Logic.Tso.History
