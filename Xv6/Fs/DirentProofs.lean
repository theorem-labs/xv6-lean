import Xv6.Fs.DirentDefs
import Lean.Util.CollectAxioms
import Lean.Elab.Command

namespace Xv6.Fs

theorem direntBytes_length (d : Dirent) (wf : d.WellFormed) : (direntBytes d).length = 16 := by
  simp [direntBytes, halfBytes, Dirent.WellFormed] at wf ⊢
  omega

theorem cutNul_length (bytes : List (BitVec 8)) : (cutNul bytes).length ≤ bytes.length := by
  induction bytes with
  | nil => simp [cutNul]
  | cons b bs ih =>
    unfold cutNul
    split <;> simp_all

theorem cutNul_no_zero (bytes : List (BitVec 8)) : ∀ b ∈ cutNul bytes, b ≠ 0 := by
  induction bytes with
  | nil => simp [cutNul]
  | cons b bs ih =>
    unfold cutNul
    split
    · simp
    · rename_i nz
      simp only [List.mem_cons]
      intro x h
      rcases h with rfl | h
      · simpa using nz
      · exact ih x h

theorem bname_length n f : (bname n f).length ≤ n := by
  have h := cutNul_length ((List.range n).map f)
  simpa [bname] using h

theorem bname_ext n f g (eq : ∀ j < n, f j = g j) : bname n f = bname n g := by
  unfold bname
  congr 1
  apply List.map_congr_left
  intro i hi
  exact eq i (List.mem_range.mp hi)

theorem dFirst_none (p : Nat → Bool) (n : Nat) :
    dFirst p n = none ↔ ∀ j < n, p j = false := by
  induction n with
  | zero => simp [dFirst]
  | succ n ih =>
    constructor
    · intro h j hj
      simp only [dFirst] at h
      cases prev : dFirst p n with
      | some k => simp [prev] at h
      | none =>
        have pn : p n = false := by cases hn : p n <;> simp_all
        by_cases eq : j = n
        · simpa [eq] using pn
        · exact ih.mp prev j (by omega)
    · intro h
      have prev := ih.mpr (fun j hj => h j (by omega))
      simp [dFirst, prev, h n (by omega)]

theorem dFirst_some (p : Nat → Bool) (n k : Nat) :
    dFirst p n = some k ↔ k < n ∧ p k = true ∧ ∀ j < k, p j = false := by
  induction n with
  | zero => simp [dFirst]
  | succ n ih =>
    constructor
    · intro h
      simp only [dFirst] at h
      cases prev : dFirst p n with
      | some old =>
        simp only [prev, Option.some.injEq] at h
        subst old
        obtain ⟨bound, hit, earlier⟩ := ih.mp prev
        exact ⟨by omega, hit, earlier⟩
      | none =>
        simp only [prev] at h
        split at h
        · cases h
          exact ⟨by omega, by assumption, (dFirst_none p k).mp prev⟩
        · contradiction
    · rintro ⟨bound, hit, earlier⟩
      by_cases eq : k = n
      · subst k
        have prev := (dFirst_none p n).mpr earlier
        simp [dFirst, prev, hit]
      · have prev := ih.mpr ⟨by omega, hit, earlier⟩
        simp [dFirst, prev]

theorem dFirst_mono p n m k (le : n ≤ m) (found : dFirst p n = some k) :
    dFirst p m = some k := by
  obtain ⟨bound, hit, earlier⟩ := (dFirst_some p n k).mp found
  exact (dFirst_some p m k).mpr ⟨by omega, hit, earlier⟩

theorem dFirst_ext p q n (eq : ∀ j < n, p j = q j) : dFirst p n = dFirst q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have tail := ih (fun j hj => eq j (by omega))
    simp only [dFirst, tail, eq n (by omega)]

theorem dirFreeb_true data k : dirFreeb data k = true ↔ dirInum data k = 0 := by
  simp [dirFreeb]

theorem dirLiveb_true data k : dirLiveb data k = true ↔ DirLive data k := by
  simp [dirLiveb, dirFreeb, DirLive]

theorem dirMatchb_true data k name : dirMatchb data k name = true ↔ DirMatch data k name := by
  simp [dirMatchb, DirMatch, dirLiveb_true]

theorem dirFirst_some data n name k : dirFirst data n name = some k ↔
    k < n ∧ DirMatch data k name ∧ ∀ j < k, ¬ DirMatch data j name := by
  rw [dirFirst, dFirst_some]
  simp only [← dirMatchb_true, Bool.eq_false_iff]

theorem dirFirst_none data n name : dirFirst data n name = none ↔
    ∀ j < n, ¬ DirMatch data j name := by
  rw [dirFirst, dFirst_none]
  simp only [← dirMatchb_true, Bool.eq_false_iff]

theorem dirFirst_lt data n name k (found : dirFirst data n name = some k) : k < n :=
  ((dirFirst_some data n name k).mp found).1

theorem dirFirst_live data n name k (found : dirFirst data n name = some k) : DirLive data k :=
  ((dirFirst_some data n name k).mp found).2.1.1

theorem dirFirst_name data n name k (found : dirFirst data n name = some k) : dirBname data k = name :=
  ((dirFirst_some data n name k).mp found).2.1.2

theorem dirWins_true data k : dirWins data k = true ↔
    DirLive data k ∧ dirFirst data k (dirBname data k) = none := by
  simp [dirWins, dirLiveb_true]

theorem dirFirst_wins data n k (bound : k < n) :
    dirFirst data n (dirBname data k) = some k ↔ dirWins data k = true := by
  rw [dirFirst_some, dirWins_true, dirFirst_none]
  simp [DirMatch, bound]

theorem nameMap_fold_lookup (entries : List (FName × Int)) (acc : NameMap) (key : FName) :
    (entries.foldr (fun entry map => map.insert entry.1 entry.2) acc)[key]? =
      match (nameMap entries)[key]? with
      | some value => some value
      | none => acc[key]? := by
  induction entries with
  | nil => simp [nameMap]
  | cons entry entries ih =>
    simp only [List.foldr_cons, nameMap, Std.ExtTreeMap.getElem?_insert,
      Std.compare_eq_eq_iff_eq] at *
    split <;> simp_all

theorem nameMap_append_lookup (left right : List (FName × Int)) (key : FName) :
    (nameMap (left ++ right))[key]? =
      match (nameMap left)[key]? with
      | some value => some value
      | none => (nameMap right)[key]? := by
  unfold nameMap
  rw [List.foldr_append]
  exact nameMap_fold_lookup left _ key

theorem dirView_succ_lookup data n name :
    (dirView data (n + 1))[name]? =
      match (dirView data n)[name]? with
      | some value => some value
      | none => if dirWins data n && (dirBname data n == name)
          then some ((dirInum data n).toNat : Int) else none := by
  unfold dirView
  rw [List.range_succ, List.filterMap_append, nameMap_append_lookup]
  cases h : (nameMap ((List.range n).filterMap (dirEntry data)))[name]? with
  | some value => rfl
  | none =>
    cases wins : dirWins data n <;>
      simp [dirEntry, wins, nameMap, Std.ExtTreeMap.getElem?_insert]

theorem dirView_lookup data n name : (dirView data n)[name]? =
    (dirFirst data n name).map (fun k => ((dirInum data k).toNat : Int)) := by
  induction n with
  | zero => simp [dirView, nameMap, dirFirst, dFirst]
  | succ n ih =>
    rw [dirView_succ_lookup, ih]
    have step : dirFirst data (n + 1) name =
      (match dirFirst data n name with
      | some k => some k
      | none => if dirMatchb data n name then some n else none) := rfl
    rw [step]
    cases first : dirFirst data n name with
    | some k => rfl
    | none =>
      cases hit : dirMatchb data n name with
      | true =>
        obtain ⟨live, nameEq⟩ := (dirMatchb_true data n name).mp hit
        have wins : dirWins data n = true := (dirWins_true data n).mpr ⟨live, by simpa [nameEq] using first⟩
        simp [wins, nameEq]
      | false =>
        have miss : ¬ (dirWins data n = true ∧ dirBname data n = name) := by
          rintro ⟨wins, nameEq⟩
          have matchTrue := (dirMatchb_true data n name).mpr ⟨((dirWins_true data n).mp wins).1, nameEq⟩
          simp [hit] at matchTrue
        simp [miss]

theorem dirView_lookup_some data n name value : (dirView data n)[name]? = some value ↔
    ∃ k, dirFirst data n name = some k ∧ ((dirInum data k).toNat : Int) = value := by
  rw [dirView_lookup]
  cases dirFirst data n name <;> simp

theorem dirView_lookup_none data n name : (dirView data n)[name]? = none ↔ dirFirst data n name = none := by
  rw [dirView_lookup]
  cases dirFirst data n name <;> simp

theorem dirView_lookup_rec data n name value (found : (dirView data n)[name]? = some value) :
    ∃ k, k < n ∧ DirLive data k ∧ dirBname data k = name ∧ ((dirInum data k).toNat : Int) = value := by
  obtain ⟨k, first, valueEq⟩ := (dirView_lookup_some data n name value).mp found
  exact ⟨k, dirFirst_lt data n name k first, dirFirst_live data n name k first,
    dirFirst_name data n name k first, valueEq⟩

theorem dirNamesUnique_le data n m (le : n ≤ m) (unique : DirNamesUnique data m) :
    DirNamesUnique data n := by
  intro j k hj hk livej livek same
  exact unique j k (by omega) (by omega) livej livek same

theorem dirView_live_some data n k (bound : k < n) (live : DirLive data k) :
    ∃ value, (dirView data n)[dirBname data k]? = some value := by
  cases first : dirFirst data n (dirBname data k) with
  | none =>
    exact False.elim (((dirFirst_none data n (dirBname data k)).mp first) k bound ⟨live, rfl⟩)
  | some j =>
    exact ⟨_, (dirView_lookup_some data n (dirBname data k) _).mpr ⟨j, first, rfl⟩⟩

theorem dirView_live_value data n k (unique : DirNamesUnique data n)
    (bound : k < n) (live : DirLive data k) :
    (dirView data n)[dirBname data k]? = some ((dirInum data k).toNat : Int) := by
  obtain ⟨value, found⟩ := dirView_live_some data n k bound live
  obtain ⟨j, first, valueEq⟩ := (dirView_lookup_some data n (dirBname data k) value).mp found
  have same := unique j k (dirFirst_lt data n _ j first) bound
    (dirFirst_live data n _ j first) live (dirFirst_name data n _ j first)
  subst j
  simpa [valueEq] using found

theorem dirInum_first_encoded (d : Dirent) : dirInum (fun _ => direntBytes d) 0 = d.inum := by
  simpa [dirInum, fileByte, direntBytes, halfBytes, byteAt, wordBytes, List.range_succ] using
    (wordBytes_decode (n := 2) d.inum)

theorem dirName_first_encoded (d : Dirent) (j : Nat) (bound : j < 14) :
    dirName (fun _ => direntBytes d) 0 j = byteAt d.name j := by
  simp only [dirName, fileByte, Nat.mul_zero, Nat.zero_add,
    Nat.mod_eq_of_lt (show 2 + j < 1024 by omega)]
  exact byteAt_append_right (halfBytes d.inum) d.name j

theorem dirInum_block_boundary (data : FileData) : dirInum data 64 =
    BitVec.ofNat 16 (MachCSL.Memory.assembleBytes [byteAt (data 1) 0, byteAt (data 1) 1]) := by
  rfl

theorem canonical_name_nul_regression : cutNul [65, 0, 255] = [65] := by decide

theorem canonical_name_cap_regression :
    bname 14 (fun j => BitVec.ofNat 8 (j + 1)) = [1,2,3,4,5,6,7,8,9,10,11,12,13,14] := by decide

private def shadowData (firstInum : BitVec 16) : FileData := fun block =>
  if block = 0 then
    direntBytes ⟨firstInum, [65,0] ++ List.replicate 12 255⟩ ++
    direntBytes ⟨2, [65,0] ++ List.replicate 12 127⟩
  else []

/-- Canonical equality stops at NUL; two live duplicates retain the first value. -/
theorem first_match_shadow_regression : (dirView (shadowData 1) 2)[([65] : FName)]? = some 1 := by decide

/-- Free records may retain arbitrary name bytes, and do not mask a later live entry. -/
theorem free_name_garbage_regression : (dirView (shadowData 0) 2)[([65] : FName)]? = some 2 := by decide

theorem first_match_scan_regression : dirFirst (shadowData 1) 2 [65] = some 0 := by decide

theorem duplicate_names_not_unique : ¬ DirNamesUnique (shadowData 1) 2 := by
  intro unique
  have impossible := unique 0 1 (by decide) (by decide)
    (by unfold DirLive; decide) (by unfold DirLive; decide) (by decide)
  contradiction

end Xv6.Fs

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs.") then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} filesystem/directory foundation theorem cones; standard foundational axioms only."
