import Xv6.Fs.DirectorySpec
import Xv6.Fs.DirentProofs

namespace Xv6.Fs

theorem uniqStep_some data k names result (h : uniqStep data k names = some result) :
    (DirLive data k ∧ dirBname data k ∉ names ∧ result = names.insert (dirBname data k)) ∨
    (¬ DirLive data k ∧ result = names) := by
  unfold uniqStep at h
  split at h
  · rename_i live
    split at h
    · contradiction
    · rename_i absent
      cases h
      exact Or.inl ⟨(dirLiveb_true data k).mp live, absent, rfl⟩
  · rename_i free
    cases h
    exact Or.inr ⟨fun live => free ((dirLiveb_true data k).mpr live), rfl⟩

theorem dirUniqb_mem data n names (h : dirUniqb data n = some names) (name : FName) :
    name ∈ names ↔ ∃ k, k < n ∧ DirLive data k ∧ dirBname data k = name := by
  induction n generalizing names with
  | zero =>
    simp only [dirUniqb, Option.some.injEq] at h
    subst names
    simp
  | succ n ih =>
    simp only [dirUniqb] at h
    cases prev : dirUniqb data n with
    | none => simp [prev] at h
    | some old =>
      simp only [prev] at h
      rcases uniqStep_some data n old names h with ⟨live, absent, rfl⟩ | ⟨free, rfl⟩
      · rw [Std.ExtTreeSet.mem_insert, Std.compare_eq_eq_iff_eq, ih old prev]
        constructor
        · rintro (eq | ⟨k, hk, hl, he⟩)
          · exact ⟨n, by omega, live, eq⟩
          · exact ⟨k, by omega, hl, he⟩
        · rintro ⟨k, hk, hl, he⟩
          by_cases eq : k = n
          · subst k; exact Or.inl he
          · exact Or.inr ⟨k, by omega, hl, he⟩
      · rw [ih _ prev]
        constructor
        · rintro ⟨k, hk, hl, he⟩; exact ⟨k, by omega, hl, he⟩
        · rintro ⟨k, hk, hl, he⟩
          have ne : k ≠ n := by intro eq; subst k; exact free hl
          exact ⟨k, by omega, hl, he⟩

theorem dirUniqb_unique data n names (h : dirUniqb data n = some names) : DirNamesUnique data n := by
  induction n generalizing names with
  | zero => intro j k hj; omega
  | succ n ih =>
    simp only [dirUniqb] at h
    cases prev : dirUniqb data n with
    | none => simp [prev] at h
    | some old =>
      simp only [prev] at h
      have earlier := ih old prev
      rcases uniqStep_some data n old names h with ⟨live, absent, _⟩ | ⟨free, _⟩
      · have noEarlier : ∀ k < n, DirLive data k → dirBname data k ≠ dirBname data n := by
          intro k hk hl same
          exact absent ((dirUniqb_mem data n old prev _).mpr ⟨k, hk, hl, same⟩)
        intro j k hj hk livej livek same
        by_cases je : j = n
        · subst j
          by_cases ke : k = n
          · exact ke.symm
          · exact False.elim (noEarlier k (by omega) livek same.symm)
        · by_cases ke : k = n
          · subst k; exact False.elim (noEarlier j (by omega) livej same)
          · exact earlier j k (by omega) (by omega) livej livek same
      · intro j k hj hk livej livek same
        have jne : j ≠ n := by intro eq; subst j; exact free livej
        have kne : k ≠ n := by intro eq; subst k; exact free livek
        exact earlier j k (by omega) (by omega) livej livek same

theorem dirUniqb_exists data n : (∃ names, dirUniqb data n = some names) ↔ DirNamesUnique data n := by
  constructor
  · rintro ⟨names, h⟩; exact dirUniqb_unique data n names h
  · intro unique
    induction n with
    | zero => exact ⟨∅, rfl⟩
    | succ n ih =>
      obtain ⟨names, prev⟩ := ih (dirNamesUnique_le data n (n + 1) (by omega) unique)
      cases live : dirLiveb data n with
      | false => exact ⟨names, by simp [dirUniqb, prev, uniqStep, live]⟩
      | true =>
        have absent : dirBname data n ∉ names := by
          intro member
          obtain ⟨k, bound, livek, same⟩ := (dirUniqb_mem data n names prev _).mp member
          have eq := unique k n (by omega) (by omega) livek ((dirLiveb_true data n).mp live) same
          omega
        exact ⟨names.insert (dirBname data n), by simp [dirUniqb, prev, uniqStep, live, absent]⟩

theorem dirUniqb_isSome data n : (dirUniqb data n).isSome = true ↔ DirNamesUnique data n := by
  rw [Option.isSome_iff_exists, dirUniqb_exists]

theorem dirValid_ok image sb self dn (valid : dirValid image sb self dn = true) :
    DirectoryOK image sb self dn := by
  unfold dirValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨⟨⟨⟨gran, entries⟩, unique⟩, dot⟩, dotdot⟩ := valid
  constructor
  · exact Int.dvd_of_emod_eq_zero (beq_iff_eq.mp gran)
  · intro k bound live
    have entry := List.all_eq_true.mp entries k (List.mem_range.mpr bound)
    have liveb := (dirLiveb_true (dataOf image dn) k).mpr live
    simpa only [liveb, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne] using entry
  · exact (dirUniqb_isSome _ _).mp unique
  · cases first : dirFirst (dataOf image dn) (dirNrec dn.sizeZ) dotName with
    | none => simp [first] at dot
    | some k =>
      rw [dirView_lookup, first]
      simp only [first] at dot
      simp only [Option.map_some]
      exact congrArg some (beq_iff_eq.mp dot)
  · obtain ⟨k, first⟩ := Option.isSome_iff_exists.mp dotdot
    exact ⟨_, (dirView_lookup_some _ _ _ _).mpr ⟨k, first, rfl⟩⟩

theorem dirValid_of_ok image sb self dn (ok : DirectoryOK image sb self dn) :
    dirValid image sb self dn = true := by
  unfold dirValid
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, (dirUniqb_isSome _ _).mpr ok.unique⟩, ?_⟩, ?_⟩
  · exact beq_iff_eq.mpr (Int.emod_eq_zero_of_dvd ok.gran)
  · apply List.all_eq_true.mpr
    intro k hk
    by_cases live : DirLive (dataOf image dn) k
    · have fields := ok.ent k (List.mem_range.mp hk) live
      have liveb := (dirLiveb_true _ _).mpr live
      simpa only [liveb, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne] using fields
    · have free : dirLiveb (dataOf image dn) k = false := by
        cases h : dirLiveb (dataOf image dn) k
        · rfl
        · exact False.elim (live ((dirLiveb_true _ _).mp h))
      simp [free]
  · obtain ⟨k, first, value⟩ := (dirView_lookup_some _ _ _ _).mp ok.dot
    rw [first]
    exact beq_iff_eq.mpr value
  · obtain ⟨value, found⟩ := ok.dotdot
    obtain ⟨k, first, _⟩ := (dirView_lookup_some _ _ _ _).mp found
    exact Option.isSome_iff_exists.mpr ⟨k, first⟩

theorem dirValid_iff image sb self dn : dirValid image sb self dn = true ↔ DirectoryOK image sb self dn :=
  ⟨dirValid_ok image sb self dn, dirValid_of_ok image sb self dn⟩

theorem directory_ok_inums image sb self dn (nib : Nat) (ok : DirectoryOK image sb self dn)
    (covered : sb.ninodes ≤ 16 * (nib : Int)) :
    DirInumsOK (dataOf image dn) (dirNrec dn.sizeZ) nib := by
  intro k hk live
  have h := (ok.ent k hk live).1.2
  omega

theorem dirsValid_spec image sb (valid : dirsValid image sb = true) (i : Int)
    (bound : 0 ≤ i ∧ i < sb.ninodes) (directory : (dinode image sb i).typeZ = 1) :
    DirectoryOK image sb i (dinode image sb i) := by
  apply dirValid_ok
  have h := List.all_eq_true.mp valid i.toNat (List.mem_range.mpr (by omega))
  have cast : (i.toNat : Int) = i := Int.toNat_of_nonneg bound.1
  simpa only [cast, directory, BEq.rfl, ↓reduceIte] using h

theorem dotsValid_ok image self dn (valid : dotsValid image self dn = true) :
    DirDotsIx self dn (dataOf image dn) := by
  unfold dotsValid at valid
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, dirLiveb_true] at valid
  obtain ⟨⟨⟨⟨⟨count, live0⟩, inum⟩, dot⟩, live1⟩, dotdot⟩ := valid
  intro _ _
  exact ⟨count, live0, inum, dot, live1, dotdot⟩

theorem dotsAll_spec image sb (valid : dotsAll image sb = true) (i : Int)
    (bound : 0 ≤ i ∧ i < sb.ninodes) (directory : (dinode image sb i).typeZ = 1) :
    DirDotsIx i (dinode image sb i) (dataOf image (dinode image sb i)) := by
  apply dotsValid_ok
  have h := List.all_eq_true.mp valid i.toNat (List.mem_range.mpr (by omega))
  have cast : (i.toNat : Int) = i := Int.toNat_of_nonneg bound.1
  simpa only [cast, directory, BEq.rfl, ↓reduceIte] using h

theorem rootValid_type image sb (valid : rootValid image sb = true) :
    (dinode image sb 1).typeZ = 1 := by
  exact beq_iff_eq.mp ((Bool.and_eq_true _ _).mp valid).1

theorem rootValid_dotdot image sb (valid : rootValid image sb = true) :
    (dirView (dataOf image (dinode image sb 1)) (dirNrec (dinode image sb 1).sizeZ))[dotdotName]? = some 1 := by
  have h := ((Bool.and_eq_true _ _).mp valid).2
  cases first : dirFirst (dataOf image (dinode image sb 1)) (dirNrec (dinode image sb 1).sizeZ) dotdotName with
  | none => simp [first] at h
  | some k =>
    simp only [first] at h
    exact (dirView_lookup_some _ _ _ _).mpr ⟨k, first, beq_iff_eq.mp h⟩

theorem dirUniqb_none data n : dirUniqb data n = none ↔ ¬ DirNamesUnique data n := by
  rw [← dirUniqb_exists]
  cases dirUniqb data n <;> simp

theorem dirsValid_negative_count image sb (count : sb.ninodes ≤ 0) : dirsValid image sb = true := by
  have zero : sb.ninodes.toNat = 0 := by omega
  simp [dirsValid, zero]

theorem dotsAll_negative_count image sb (count : sb.ninodes ≤ 0) : dotsAll image sb = true := by
  have zero : sb.ninodes.toNat = 0 := by omega
  simp [dotsAll, zero]

private def swappedDotRecord : Dinode := ⟨1, 0, 0, 1, 32, [47] ++ List.replicate 12 0⟩
private def swappedDotSb : Superblock := ⟨0, 2000, 0, 2, 0, 0, 33, 46⟩
private def swappedDotImage (targetType : BitVec 16) : Blocks := fun block =>
  if block = 33 then inodeBlockBytes
    [⟨0,0,0,0,0,List.replicate 13 0⟩, { swappedDotRecord with type := targetType }]
  else if block = 47 then
    direntBytes ⟨1, [46,46,0] ++ List.replicate 11 255⟩ ++
    direntBytes ⟨1, [46,0] ++ List.replicate 12 127⟩
  else []

/-- W6 scans names: it accepts dots at different indices, so W8 is essential. -/
theorem swapped_dots_directory_valid :
    dirValid (swappedDotImage 1) swappedDotSb 1 swappedDotRecord = true := by decide

theorem swapped_dots_index_invalid : dotsValid (swappedDotImage 1) 1 swappedDotRecord = false := by decide

theorem live_entry_dead_target_rejected :
    dirValid (swappedDotImage 0) swappedDotSb 1 swappedDotRecord = false := by decide

theorem swapped_dots_root_valid : rootValid (swappedDotImage 1) swappedDotSb = true := by decide

private def sameNameData (first : BitVec 16) : FileData := fun _ =>
  direntBytes ⟨first, [65,0] ++ List.replicate 12 255⟩ ++
  direntBytes ⟨2, [65,0] ++ List.replicate 12 127⟩

theorem live_duplicate_names_rejected : dirUniqb (sameNameData 1) 2 = none := by decide

theorem free_duplicate_names_accepted : (dirUniqb (sameNameData 0) 2).isSome = true := by decide

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
  logInfo m!"Audited {count} filesystem/directory theorem cones; standard foundational axioms only."
