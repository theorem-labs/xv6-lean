import Xv6.Fs.RecoverySpec
import Xv6.Fs.SnapshotHomeProofs

namespace Xv6.Fs.Recovery
open MachCSL.Memory

theorem headerN_nonnegative bytes : 0 ≤ headerN bytes := Int.natCast_nonneg _
theorem headerWord_zero bytes : headerWord bytes 0 = headerN bytes := by
  simp [headerWord, headerN]
theorem headerDecode_count bytes : ((headerDecode bytes).1 : Int) = headerN bytes := by
  simp only [headerDecode, headerWord_zero]
  exact Int.toNat_of_nonneg (headerN_nonnegative bytes)
theorem headerDecode_length bytes : (headerDecode bytes).2.length = (headerDecode bytes).1 := by
  simp [headerDecode]
theorem headerDecode_zero bytes (zero : headerN bytes = 0) : headerDecode bytes = (0, []) := by
  simp [headerDecode, headerWord_zero, zero]
theorem headerWF_zero physical coverage start
    (zero : headerN (physical (SnapshotHome.logHeader start)) = 0) :
    HeaderWF physical coverage start := by
  constructor
  · rw [headerDecode_zero _ zero]; decide
  · rw [headerDecode_zero _ zero]; exact List.nodup_nil
  · rw [headerDecode_zero _ zero]; simp

theorem codecSpec : CodecSpec :=
  ⟨headerN_nonnegative, headerWord_zero, headerDecode_count, headerDecode_length,
    headerDecode_zero, headerWF_zero⟩

theorem installStep_some physical start writes i disk b (found : writes[i]? = some b) :
    installStep physical start writes i disk = disk.insert b (physical (SnapshotHome.logSlot start i)) := by
  simp [installStep, found]
theorem installStep_none physical start writes i disk (absent : writes[i]? = none) :
    installStep physical start writes i disk = disk := by simp [installStep, absent]

theorem install_fold_miss physical start (writes : List Int) disk (indices : List Nat) b
    (outside : b ∉ writes) :
    (indices.foldr (installStep physical start writes) disk)[b]? = disk[b]? := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldr_cons]
    cases found : writes[i]? with
    | none => rw [installStep_none _ _ _ _ _ found, ih]
    | some c =>
      have ne : c ≠ b := by
        intro eq
        exact outside (eq ▸ List.mem_of_getElem? found)
      rw [installStep_some _ _ _ _ _ _ found, Std.ExtTreeMap.getElem?_insert]
      simpa [ne] using ih

theorem install_fold_hit physical start (writes : List Int) disk (indices : List Nat) i b
    (distinct : writes.Nodup) (found : writes[i]? = some b) (member : i ∈ indices) :
    (indices.foldr (installStep physical start writes) disk)[b]? =
      some (physical (SnapshotHome.logSlot start i)) := by
  induction indices with
  | nil => simp at member
  | cons j indices ih =>
    rw [List.foldr_cons]
    cases other : writes[j]? with
    | none =>
      rw [installStep_none _ _ _ _ _ other]
      apply ih
      rcases List.mem_cons.mp member with eq | mem
      · subst j; rw [found] at other; cases other
      · exact mem
    | some c =>
      rw [installStep_some _ _ _ _ _ _ other, Std.ExtTreeMap.getElem?_insert]
      by_cases same : c = b
      · subst c
        have ji : j = i := (List.getElem?_inj
          (List.getElem?_eq_some_iff.mp other).1 distinct).mp (other.trans found.symm)
        subst j
        simp
      · simp only [Std.compare_eq_eq_iff_eq, same, ↓reduceIte]
        apply ih
        rcases List.mem_cons.mp member with eq | mem
        · subst j; rw [found] at other; exact False.elim (same (Option.some.inj other.symm))
        · exact mem

theorem install_miss physical start writes disk b (outside : b ∉ writes) :
    (install physical start writes disk)[b]? = disk[b]? :=
  install_fold_miss physical start writes disk _ b outside

theorem install_hit physical start writes disk i b (distinct : writes.Nodup)
    (found : writes[i]? = some b) :
    (install physical start writes disk)[b]? = some (physical (SnapshotHome.logSlot start i)) :=
  install_fold_hit physical start writes disk _ i b distinct found
    (List.mem_range.mpr (List.getElem?_eq_some_iff.mp found).1)

theorem install_fold_full (physical : Blocks) start (writes : List Int) disk (indices : List Nat)
    (allFull : ∀ b, (physical b).length = 1024) (full : Full disk) :
    Full (indices.foldr (installStep physical start writes) disk) := by
  induction indices with
  | nil => exact full
  | cons i indices ih =>
    rw [List.foldr_cons]
    cases found : writes[i]? with
    | none => rw [installStep_none _ _ _ _ _ found]; exact ih
    | some c =>
      rw [installStep_some _ _ _ _ _ _ found]
      intro b bytes lookup
      rw [Std.ExtTreeMap.getElem?_insert] at lookup
      by_cases same : c = b
      · simp only [Std.compare_eq_eq_iff_eq, same, ↓reduceIte] at lookup
        cases lookup
        exact allFull _
      · simp only [Std.compare_eq_eq_iff_eq, same, ↓reduceIte] at lookup
        exact ih b bytes lookup

theorem install_full (physical : Blocks) start writes disk
    (allFull : ∀ b, (physical b).length = 1024) (full : Full disk) :
    Full (install physical start writes disk) := install_fold_full physical start writes disk _ allFull full

theorem install_idempotent physical start writes disk (distinct : writes.Nodup)
    (already : ∀ i b, writes[i]? = some b → disk[b]? = some (physical (SnapshotHome.logSlot start i))) :
    install physical start writes disk = disk := by
  apply Std.ExtTreeMap.ext_getElem?
  intro b
  by_cases member : b ∈ writes
  · obtain ⟨i, found⟩ := List.mem_iff_getElem?.mp member
    rw [install_hit _ _ _ _ _ _ distinct found, already i b found]
  · exact install_miss _ _ _ _ _ member

theorem installSpec : InstallSpec :=
  ⟨installStep_some, installStep_none, install_miss, install_hit, install_full, install_idempotent⟩

end Xv6.Fs.Recovery
