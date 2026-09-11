import Xv6.Fs.SnapshotHomeDefs
import Xv6.Fs.BootImageProofs
import Lean.Util.CollectAxioms
import Lean.Elab.Command

namespace Xv6.Fs.SnapshotHome
open DurableState

theorem logRegion_mem (start b : Int) : b ∈ logRegion start ↔ start ≤ b ∧ b < start + 31 := by
  simp only [logRegion, Std.ExtTreeSet.mem_insert, Std.compare_eq_eq_iff_eq,
    Std.ExtTreeSet.mem_ofList, List.contains_iff_mem, List.mem_map, List.mem_range, logHeader, logBlocks, logSlot]
  constructor
  · rintro (same | ⟨i, bound, eq⟩) <;> omega
  · intro bound
    by_cases same : start = b
    · exact Or.inl same
    · exact Or.inr ⟨(b - start - 1).toNat, by omega, by omega⟩

theorem logRegion_header (start : Int) : logHeader start ∈ logRegion start :=
  (logRegion_mem start start).mpr ⟨by omega, by omega⟩

theorem logRegion_slot (start : Int) (i : Nat) (bound : i < 30) : logSlot start i ∈ logRegion start := by
  apply (logRegion_mem _ _).mpr
  unfold logSlot
  constructor <;> omega

theorem logRegion_slot_injective (start : Int) (left right : Nat)
    (same : logSlot start left = logSlot start right) : left = right := by
  unfold logSlot at same
  omega

theorem logRegion_header_not_slot (start : Int) (i : Nat) : logHeader start ≠ logSlot start i := by
  unfold logHeader logSlot
  omega

theorem logRegion_last (start : Int) : start + 30 ∈ logRegion start :=
  (logRegion_mem _ _).mpr ⟨by omega, by omega⟩

theorem logRegion_after (start : Int) : start + 31 ∉ logRegion start := by
  rw [logRegion_mem]
  omega

theorem homeSet_mem (coverage : BlockSet) start b : b ∈ homeSet coverage start ↔
    b ∈ coverage ∧ ¬(start ≤ b ∧ b < start + 31) := by
  rw [homeSet, Std.ExtTreeSet.mem_diff_iff, logRegion_mem]

theorem homeSet_subset (coverage : BlockSet) start b (member : b ∈ homeSet coverage start) :
    b ∈ coverage := ((homeSet_mem _ _ _).mp member).1

theorem homeSet_not_log (coverage : BlockSet) start b (member : b ∈ homeSet coverage start) :
    b ∉ logRegion start := by
  rw [logRegion_mem]
  exact ((homeSet_mem _ _ _).mp member).2

theorem homeSet_mono (left right : BlockSet) start (subset : ∀ b, b ∈ left → b ∈ right) :
    ∀ b, b ∈ homeSet left start → b ∈ homeSet right start := by
  intro b member
  rw [homeSet_mem] at member ⊢
  exact ⟨subset b member.1, member.2⟩

theorem restrict_list_lookup (image : Blocks) (keys : List Int) (b : Int) :
    (keys.foldr (fun key (m : BlockMap) => m.insert key (image key)) ∅)[b]? =
      if b ∈ keys then some (image b) else none := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    rw [List.foldr_cons, Std.ExtTreeMap.getElem?_insert, ih]
    simp only [Std.compare_eq_eq_iff_eq, List.mem_cons]
    by_cases same : key = b
    · subst key
      simp
    · simp [same, Ne.symm same]

theorem restrict_lookup (image : Blocks) (covered : BlockSet) (b : Int) :
    (restrict image covered)[b]? = if b ∈ covered then some (image b) else none := by
  simp only [restrict, restrict_list_lookup, Std.ExtTreeSet.mem_toList]

theorem restrict_lookup_some image covered (b : Int) bytes :
    (restrict image covered)[b]? = some bytes ↔ b ∈ covered ∧ bytes = image b := by
  rw [restrict_lookup]
  split <;> simp_all [eq_comm]

theorem restrict_lookup_none image covered (b : Int) :
    (restrict image covered)[b]? = none ↔ b ∉ covered := by
  rw [restrict_lookup]
  split <;> simp_all

theorem restrict_domain image covered (b : Int) : (restrict image covered)[b]?.isSome ↔ b ∈ covered := by
  rw [restrict_lookup]
  split <;> simp_all

theorem restrict_enumeration image covered (keys : List Int)
    (same : ∀ b, b ∈ keys ↔ b ∈ covered) :
    keys.foldr (fun b (m : BlockMap) => m.insert b (image b)) ∅ = restrict image covered := by
  apply Std.ExtTreeMap.ext_getElem?
  intro b
  simp only [restrict_list_lookup, restrict_lookup, same]

theorem view_found (disk : BlockMap) (b : Int) bytes (found : disk[b]? = some bytes) : view disk b = bytes := by
  simp [view, found]

theorem view_absent (disk : BlockMap) (b : Int) (absent : disk[b]? = none) : view disk b = [] := by
  simp [view, absent]

theorem view_restrict image covered (b : Int) :
    view (restrict image covered) b = if b ∈ covered then image b else [] := by
  rw [view, restrict_lookup]
  split <;> rfl

theorem restrict_view (disk : BlockMap) (covered : BlockSet)
    (domain : ∀ b : Int, disk[b]?.isSome ↔ b ∈ covered) : restrict (view disk) covered = disk := by
  apply Std.ExtTreeMap.ext_getElem?
  intro b
  rw [restrict_lookup]
  cases found : disk[b]? with
  | none =>
    have absent : b ∉ covered := by rw [← domain b, found]; simp
    rw [if_neg absent]
  | some bytes =>
    have member : b ∈ covered := (domain b).mp (by rw [found]; rfl)
    rw [if_pos member, view_found disk b bytes found]

theorem homeMap_lookup image coverage start (b : Int) :
    (homeMap image coverage start)[b]? =
      if b ∈ coverage ∧ ¬(start ≤ b ∧ b < start + 31) then some (image b) else none := by
  simp only [homeMap, restrict_lookup, homeSet_mem]

theorem homeMap_log_absent image coverage start (b : Int) (log : start ≤ b ∧ b < start + 31) :
    (homeMap image coverage start)[b]? = none := by
  rw [homeMap_lookup, if_neg (by simp [log])]

theorem homeMap_covIn (coverage : BlockSet) (ndisk : Nat) start (h : CovIn coverage ndisk) :
    CovIn (homeSet coverage start) ndisk :=
  covIn_mono _ _ ndisk (homeSet_subset coverage start) h

/-- Positivity is inherited from explicit coverage; homeSet itself is signed. -/
theorem homeMap_zero_absent image coverage ndisk start (covered : CovIn coverage ndisk) :
    (homeMap image coverage start)[(0 : Int)]? = none := by
  rw [homeMap_lookup]
  exact if_neg (by intro member; exact covIn_zero coverage ndisk covered member.1)

theorem homeMap_below image coverage ndisk start (sb : Superblock) (covered : CovIn coverage ndisk)
    (diskBound : (ndisk : Int) ≤ 1024 * sb.size) (b : Int)
    (present : (homeMap image coverage start)[b]?.isSome) : 0 < b ∧ b < sb.size := by
  have member := (restrict_domain image (homeSet coverage start) b).mp present
  have h := covered b (homeSet_subset coverage start b member)
  constructor <;> omega

theorem boot_home_superblock (h : BootImageWF disk ndisk sb nib cov) :
    (1 : Int) ∈ homeSet cov sb.logstart := by
  have geometry := bootImage_superblock h
  have metaBounds := superblock_metadata sb geometry
  have := geometry.logstart
  have := geometry.nlog
  have := geometry.inodestart
  apply (homeSet_mem _ _ _).mpr
  exact ⟨h.metadata 1 ⟨by omega, by omega⟩, by omega⟩

theorem boot_home_region (h : BootImageWF disk ndisk sb nib cov) (b : Int)
    (bound : sb.inodestart ≤ b ∧ b < dataStart sb) : b ∈ homeSet cov sb.logstart := by
  have geometry := bootImage_superblock h
  have := geometry.logstart
  have := geometry.nlog
  have := geometry.inodestart
  apply (homeSet_mem _ _ _).mpr
  exact ⟨h.metadata b ⟨by omega, bound.2⟩, by omega⟩

theorem boot_home_data (h : BootImageWF disk ndisk sb nib cov) (b : Int)
    (bound : dataStart sb ≤ b ∧ b < sb.size) : b ∈ homeSet cov sb.logstart := by
  have geometry := bootImage_superblock h
  have metaBounds := superblock_metadata sb geometry
  have := geometry.nlog
  have := geometry.inodestart
  apply (homeSet_mem _ _ _).mpr
  exact ⟨h.data b bound, by omega⟩

/-- Home restriction imposes no hidden positivity filter. -/
theorem zero_coverage_preserved (image : Blocks) :
    (homeMap image (Std.ExtTreeSet.ofList [(0 : Int)]) 2)[(0 : Int)]? = some (image 0) := by
  rw [homeMap_lookup, if_pos (by decide)]

theorem negative_coverage_preserved (image : Blocks) :
    (homeMap image (Std.ExtTreeSet.ofList [(-5 : Int)]) 2)[(-5 : Int)]? = some (image (-5)) := by
  rw [homeMap_lookup, if_pos (by decide)]

end Xv6.Fs.SnapshotHome

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "Xv6.Fs.SnapshotHome." || name.toString.startsWith "_private.Xv6.Fs.SnapshotHome" then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} snapshot-home declarations; standard foundational axioms only."
