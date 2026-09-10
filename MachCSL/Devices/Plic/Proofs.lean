import MachCSL.Devices.Plic.Defs

/-! Checked properties of the PLIC transcription. The source section has no
PLIC lemmas; these verify its selection, threshold, gateway and decoder behavior.
They do not establish cross-prover correspondence or the global device fabric. -/
namespace MachCSL.Devices.Plic

@[simp] theorem nupd_same (f : Nat → α) (i : Nat) (value : α) :
    nupd f i value i = value := by simp [nupd]

@[simp] theorem nupd_other (f : Nat → α) (i j : Nat) (value : α) (h : j ≠ i) :
    nupd f i value j = f j := by simp [nupd, h]

@[simp] theorem hupd_same (f : Nat → α) (i : Nat) (value : α) :
    hupd f i value i = value := by simp [hupd]

@[simp] theorem wupd_same (f : Nat → Nat → Word) (c w : Nat) (value : Word) :
    wupd f c w value c w = value := by simp [wupd]

@[simp] theorem wupd_other (f : Nat → Nat → Word) (c w c' w' : Nat) (value : Word)
    (h : c' ≠ c ∨ w' ≠ w) : wupd f c w value c' w' = f c' w' := by
  simp only [wupd]
  split
  · rename_i h'
    rcases h with h | h <;> simp_all
  · rfl

@[simp] theorem mem_srcs {source : Nat} : source ∈ srcs ↔ 1 ≤ source ∧ source < nSrc := by
  simp only [srcs, List.mem_range', nSrc]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨hl, hu⟩
    exact ⟨source - 1, by omega, by omega⟩

theorem cand_iff (p : State) (c i : Nat) :
    cand p c i = true ↔ p.pending i = true ∧ enabled p c i = true ∧
      (p.thresh c).toNat < (p.prio i).toNat := by
  simp [cand, Bool.and_eq_true, and_assoc]

theorem cand_false_of_threshold (p : State) (c i : Nat)
    (h : (p.prio i).toNat ≤ (p.thresh c).toNat) : cand p c i = false := by
  simp [cand, Nat.not_lt.mpr h]

theorem better_iff (p : State) (i j : Nat) :
    better p i j = true ↔ (p.prio j).toNat < (p.prio i).toNat ∨
      ((p.prio i).toNat = (p.prio j).toNat ∧ i < j) := by
  simp [better]

@[simp] theorem better_irrefl (p : State) (i : Nat) : better p i i = false := by
  simp [better]

theorem better_tie (p : State) (i j : Nat) (h : p.prio i = p.prio j) :
    better p i j = decide (i < j) := by simp [better, h]

theorem better_asymm (p : State) (i j : Nat) (h : better p i j = true) :
    better p j i = false := by
  rw [Bool.eq_false_iff]
  intro h'
  rw [better_iff] at h h'
  omega

theorem better_trans (p : State) (i j k : Nat)
    (hij : better p i j = true) (hjk : better p j k = true) : better p i k = true := by
  rw [better_iff] at hij hjk ⊢
  omega

theorem select_eq_none (p : State) (c i : Nat) (winner : Option Nat) :
    select p c winner i = none ↔ winner = none ∧ cand p c i = false := by
  cases h : cand p c i <;> cases winner <;> simp [select, h]
  split <;> simp_all

theorem fold_eq_none (p : State) (c : Nat) (sources : List Nat) (winner : Option Nat) :
    sources.foldl (select p c) winner = none ↔
      winner = none ∧ ∀ i ∈ sources, cand p c i = false := by
  induction sources generalizing winner with
  | nil => simp
  | cons i rest ih =>
    simp only [List.foldl_cons, ih, select_eq_none, List.mem_cons, forall_eq_or_imp]
    exact and_assoc

theorem best_none_iff_eip_false (p : State) (c : Nat) :
    best p c = none ↔ eip p c = false := by
  simp only [best, fold_eq_none, true_and, eip, List.any_eq_false, Bool.not_eq_true]

theorem select_some_source (p : State) (c i j : Nat) (winner : Option Nat)
    (h : select p c winner i = some j) :
    winner = some j ∨ (j = i ∧ cand p c i = true) := by
  cases hc : cand p c i with
  | false => exact Or.inl (by simpa [select, hc] using h)
  | true =>
    cases winner with
    | none =>
      have hij : i = j := by simpa [select, hc] using h
      exact Or.inr ⟨hij.symm, rfl⟩
    | some old =>
      by_cases hb : better p i old = true
      · have hij : i = j := by simpa [select, hc, hb] using h
        exact Or.inr ⟨hij.symm, rfl⟩
      · exact Or.inl (by simpa [select, hc, hb] using h)

theorem fold_some_source (p : State) (c j : Nat) (sources : List Nat) (winner : Option Nat)
    (h : sources.foldl (select p c) winner = some j) :
    winner = some j ∨ (j ∈ sources ∧ cand p c j = true) := by
  induction sources generalizing winner with
  | nil => exact Or.inl h
  | cons i rest ih =>
    rcases ih (select p c winner i) h with hs | ⟨hm, hc⟩
    · rcases select_some_source p c i j winner hs with hw | ⟨rfl, hc⟩
      · exact Or.inl hw
      · exact Or.inr ⟨by simp, hc⟩
    · exact Or.inr ⟨by simp [hm], hc⟩

theorem best_some_valid (p : State) (c i : Nat) (h : best p c = some i) :
    1 ≤ i ∧ i < nSrc ∧ cand p c i = true := by
  rcases fold_some_source p c i srcs none h with hn | ⟨hi, hc⟩
  · contradiction
  · exact ⟨(mem_srcs.mp hi).1, (mem_srcs.mp hi).2, hc⟩

/-- Later fold steps cannot replace a winner by a worse source. -/
theorem fold_preserves_bound (p : State) (c i : Nat) (sources : List Nat) (old j : Nat)
    (hb : better p i old = false)
    (h : sources.foldl (select p c) (some old) = some j) : better p i j = false := by
  induction sources generalizing old with
  | nil =>
    have he : old = j := Option.some.inj h
    simpa only [← he] using hb
  | cons source rest ih =>
    by_cases hc : cand p c source = true
    · by_cases hs : better p source old = true
      · have hnew : better p i source = false := by
          rw [Bool.eq_false_iff]
          intro hi
          have := better_trans p i source old hi hs
          simp_all
        apply ih source hnew
        simpa [List.foldl_cons, select, hc, hs] using h
      · apply ih old hb
        simpa [List.foldl_cons, select, hc, hs] using h
    · apply ih old hb
      simpa [List.foldl_cons, select, hc] using h

theorem fold_dominates_candidates (p : State) (c i j : Nat) (sources : List Nat)
    (winner : Option Nat) (hi : i ∈ sources) (hc : cand p c i = true)
    (h : sources.foldl (select p c) winner = some j) : better p i j = false := by
  induction sources generalizing winner with
  | nil => simp at hi
  | cons source rest ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · cases winner with
      | none =>
        apply fold_preserves_bound p c i rest i j (better_irrefl p i)
        simpa [List.foldl_cons, select, hc] using h
      | some old =>
        by_cases hs : better p i old = true
        · apply fold_preserves_bound p c i rest i j (better_irrefl p i)
          simpa [List.foldl_cons, select, hc, hs] using h
        · apply fold_preserves_bound p c i rest old j (Bool.eq_false_iff.mpr hs)
          simpa [List.foldl_cons, select, hc, hs] using h
    · exact ih (select p c winner source) hi h

/-- The claimed winner has maximal priority; among equal priorities it has the
smallest ID. This quantifies over every visible source in the complete scan. -/
theorem best_optimal (p : State) (c winner source : Nat)
    (hb : best p c = some winner) (hl : 1 ≤ source) (hu : source < nSrc)
    (hc : cand p c source = true) :
    (p.prio source).toNat ≤ (p.prio winner).toNat ∧
      ((p.prio source).toNat = (p.prio winner).toNat → winner ≤ source) := by
  have hn := fold_dominates_candidates p c source winner srcs none
    (mem_srcs.mpr ⟨hl, hu⟩) hc hb
  rw [Bool.eq_false_iff] at hn
  simp only [ne_eq, better_iff] at hn
  omega

theorem best_some_threshold (p : State) (c i : Nat) (h : best p c = some i) :
    (p.thresh c).toNat < (p.prio i).toNat :=
  (cand_iff p c i).mp (best_some_valid p c i h).2.2 |>.2.2

theorem claim_none (p : State) (c : Nat) (h : best p c = none) : claim p c = (0, p) := by
  simp [claim, h]

theorem claim_no_interrupt (p : State) (c : Nat) (h : eip p c = false) :
    claim p c = (0, p) := claim_none p c ((best_none_iff_eip_false p c).mpr h)

theorem claim_some (p : State) (c i : Nat) (h : best p c = some i) :
    claim p c = (BitVec.ofNat 32 i,
      { p with pending := nupd p.pending i false, claimed := nupd p.claimed i true }) := by
  simp [claim, h]

theorem claim_clears_pending (p : State) (c i : Nat) (h : best p c = some i) :
    (claim p c).2.pending i = false := by simp [claim, h]

theorem claim_marks_claimed (p : State) (c i : Nat) (h : best p c = some i) :
    (claim p c).2.claimed i = true := by simp [claim, h]

theorem claim_preserves_other (p : State) (c i j : Nat) (h : best p c = some i) (hne : j ≠ i) :
    (claim p c).2.pending j = p.pending j ∧ (claim p c).2.claimed j = p.claimed j := by
  simp [claim, h, hne]

theorem complete_valid (p : State) (i : Nat) (hl : 1 ≤ i) (hu : i < nSrc) :
    complete p i = { p with claimed := nupd p.claimed i false } := by
  simp [complete, hl, hu]

theorem complete_invalid (p : State) (i : Nat) (h : i = 0 ∨ nSrc ≤ i) :
    complete p i = p := by
  rcases h with h | h
  · simp [complete, h]
  · simp [complete, Nat.not_lt.mpr h]

@[simp] theorem complete_pending (p : State) (i j : Nat) :
    (complete p i).pending j = p.pending j := by unfold complete; split <;> rfl

theorem latch_iff (p p' : State) (i : Nat) :
    latch p i = some p' ↔ p.pending i = false ∧ p.claimed i = false ∧
      p' = { p with pending := nupd p.pending i true } := by
  cases hp : p.pending i <;> cases hc : p.claimed i <;>
    simp [latch, hp, hc, eq_comm]

theorem latch_pending (p p' : State) (i : Nat) (h : latch p i = some p') :
    p'.pending i = true := by
  rcases (latch_iff p p' i).mp h with ⟨_, _, rfl⟩
  simp

theorem latch_blocked_pending (p : State) (i : Nat) (h : p.pending i = true) :
    latch p i = none := by simp [latch, h]

theorem latch_blocked_claimed (p : State) (i : Nat) (h : p.claimed i = true) :
    latch p i = none := by simp [latch, h]

@[simp] theorem initial_cand (c i : Nat) : cand initial c i = false := rfl

@[simp] theorem initial_eip (c : Nat) : eip initial c = false := by
  simp [eip, List.any_eq_false]

@[simp] theorem initial_best (c : Nat) : best initial c = none :=
  (best_none_iff_eip_false initial c).mpr (initial_eip c)

@[simp] theorem initial_claim (c : Nat) : claim initial c = (0, initial) := by
  simp [claim]


/-- A real winner's source ID fits in the returned 32-bit claim word. -/
theorem claim_id_exact (p : State) (c i : Nat) (h : best p c = some i) :
    (claim p c).1.toNat = i := by
  have hi := (best_some_valid p c i h).2.1
  rw [claim_some p c i h]
  simp only [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  simp only [nSrc] at hi
  omega

theorem prioSrc_bounds (off : Int) (i : Nat) (h : prioSrc off = some i) :
    0 ≤ off ∧ off < 4 * (nSrc : Int) ∧ off % 4 = 0 ∧ i < nSrc := by
  unfold prioSrc at h
  split at h
  · rename_i hg
    simp only [Option.some.injEq] at h
    subst i
    refine ⟨hg.1, hg.2.1, hg.2.2, ?_⟩
    simp only [nSrc] at *
    omega
  · contradiction

theorem pendingWidx_bounds (off : Int) (w : Nat) (h : pendingWidx off = some w) :
    0x1000 ≤ off ∧ off < 0x1000 + 4 * (nWords : Int) ∧ off % 4 = 0 ∧ w < nWords := by
  unfold pendingWidx at h
  split at h
  · rename_i hg
    simp only [Option.some.injEq] at h
    subst w
    refine ⟨hg.1, hg.2.1, hg.2.2, ?_⟩
    simp only [nWords] at *
    omega
  · contradiction

theorem enableCtx_bounds (off : Int) (c w : Nat) (h : enableCtx off = some (c, w)) :
    0x2000 ≤ off ∧ off < 0x2000 + 0x80 * (nCtx : Int) ∧ off % 4 = 0 ∧
      c < nCtx ∧ w < nWords := by
  unfold enableCtx at h
  split at h
  · rename_i hg
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    refine ⟨hg.1, hg.2.1, hg.2.2.1, ?_, ?_⟩ <;>
      simp only [nCtx, nCpu, nWords] at * <;> omega
  · contradiction

theorem threshCtx_bounds (off : Int) (c : Nat) (h : threshCtx off = some c) :
    0x200000 ≤ off ∧ (off - 0x200000) % 0x1000 = 0 ∧ c < nCtx := by
  unfold threshCtx at h
  split at h
  · rename_i hg
    simp only [Option.some.injEq] at h
    subst c
    refine ⟨hg.1, hg.2.1, ?_⟩
    simp only [nCtx, nCpu] at *
    omega
  · contradiction

theorem claimCtx_bounds (off : Int) (c : Nat) (h : claimCtx off = some c) :
    0x200004 ≤ off ∧ (off - 0x200004) % 0x1000 = 0 ∧ c < nCtx := by
  unfold claimCtx at h
  split at h
  · rename_i hg
    simp only [Option.some.injEq] at h
    subst c
    refine ⟨hg.1, hg.2.1, ?_⟩
    simp only [nCtx, nCpu] at *
    omega
  · contradiction

@[simp] theorem read_source_zero (p : State) : read p 0 = some (0, p) := rfl
@[simp] theorem write_source_zero (p : State) (value : Word) : write p 0 value = some p := rfl

theorem read_none_iff (p : State) (off : Int) :
    read p off = none ↔ prioSrc off = none ∧ pendingWidx off = none ∧
      enableCtx off = none ∧ threshCtx off = none ∧ claimCtx off = none := by
  unfold read
  cases hp : prioSrc off <;> cases hw : pendingWidx off <;>
    cases he : enableCtx off <;> cases ht : threshCtx off <;>
    cases hc : claimCtx off <;> simp

theorem write_none_iff (p : State) (off : Int) (value : Word) :
    write p off value = none ↔ prioSrc off = none ∧ pendingWidx off = none ∧
      enableCtx off = none ∧ threshCtx off = none ∧ claimCtx off = none := by
  unfold write
  cases hp : prioSrc off <;> cases hw : pendingWidx off <;>
    cases he : enableCtx off <;> cases ht : threshCtx off <;>
    cases hc : claimCtx off <;> simp

theorem read_none_iff_write_none (p : State) (off : Int) (value : Word) :
    read p off = none ↔ write p off value = none :=
  (read_none_iff p off).trans (write_none_iff p off value).symm

/-- Signed negative offsets are rejected rather than truncated to address zero. -/
theorem negative_offset (p : State) (off : Int) (value : Word) (h : off < 0) :
    read p off = none ∧ write p off value = none := by
  have hp : prioSrc off = none := by simp [prioSrc, show ¬0 ≤ off by omega]
  have hw : pendingWidx off = none := by simp [pendingWidx, show ¬0x1000 ≤ off by omega]
  have he : enableCtx off = none := by simp [enableCtx, show ¬0x2000 ≤ off by omega]
  have ht : threshCtx off = none := by simp [threshCtx, show ¬0x200000 ≤ off by omega]
  have hc : claimCtx off = none := by simp [claimCtx, show ¬0x200004 ≤ off by omega]
  exact ⟨(read_none_iff p off).mpr ⟨hp, hw, he, ht, hc⟩,
    (write_none_iff p off value).mpr ⟨hp, hw, he, ht, hc⟩⟩

/-- A claim prevents the gateway from forwarding that source again until completion. -/
theorem claim_blocks_latch (p : State) (c i : Nat) (h : best p c = some i) :
    latch (claim p c).2 i = none :=
  latch_blocked_claimed _ _ (claim_marks_claimed p c i h)

/-- Completion releases a claimed source; with its cleared pending bit, it can
be latched again. The board, not this helper, supplies the interrupt level. -/
theorem completion_allows_relatch (p : State) (c i : Nat) (h : best p c = some i) :
    ∃ next, latch (complete (claim p c).2 i) i = some next := by
  have hv := best_some_valid p c i h
  simp [claim, h, complete, hv.1, hv.2.1, latch]

@[simp] theorem initial_pendingWord (word : Nat) : pendingWord initial word = 0 := rfl

/-- Pending words are read-only throughout their decoded range. -/
theorem write_pending_readonly (p : State) (off : Int) (word : Nat) (value : Word)
    (h : pendingWidx off = some word) : write p off value = some p := by
  have hlo := (pendingWidx_bounds off word h).1
  have hp : prioSrc off = none := by
    unfold prioSrc
    have hhi : ¬off < 4 * (nSrc : Int) := by simp only [nSrc]; omega
    simp [hhi]
  simp [write, hp, h]

end MachCSL.Devices.Plic
