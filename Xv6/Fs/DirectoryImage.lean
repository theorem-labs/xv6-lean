import Xv6.Fs.DirectoryData

/-! W6–W8 certificates for the actual pinned initial disk. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Xv6.Fs.Image
open Xv6.Generated.InodeW3

theorem root_directory_entry_bounds : (List.range 64).all (fun k =>
    !dirLiveb rootDirectoryData k ||
    decide (1 ≤ ((dirInum rootDirectoryData k).toNat : Int) ∧
      ((dirInum rootDirectoryData k).toNat : Int) ≤ 22)) = true := by decide

theorem root_directory_unique : DirNamesUnique rootDirectoryData 64 :=
  (dirUniqb_isSome _ _).mp (by decide)

theorem root_directory_dot : (dirView rootDirectoryData 64)[dotName]? = some 1 := by
  rw [dirView_lookup]
  decide

theorem root_directory_dotdot : (dirView rootDirectoryData 64)[dotdotName]? = some 1 := by
  rw [dirView_lookup]
  decide

theorem root_directory_ok : DirectoryOK blockView superblock 1 record01 := by
  apply directoryOK_of_data_eq blockView superblock 1 record01 rootDirectoryData root_directory_data
  · decide
  · intro k bound live
    have checked := List.all_eq_true.mp root_directory_entry_bounds k (List.mem_range.mpr bound)
    have alive : dirLiveb rootDirectoryData k = true := (dirLiveb_true _ _).mpr live
    rw [alive] at checked
    have limits : 1 ≤ ((dirInum rootDirectoryData k).toNat : Int) ∧
        ((dirInum rootDirectoryData k).toNat : Int) ≤ 22 := of_decide_eq_true checked
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · change ((dirInum rootDirectoryData k).toNat : Int) < 200
      omega
    · exact ((liveSet_mem blockView superblock _).mp
        ((live_set_membership _).mpr limits)).2
  · exact root_directory_unique
  · exact root_directory_dot
  · exact ⟨1, root_directory_dotdot⟩

theorem root_dir_valid_checked : dirValid blockView superblock 1 (dinode blockView superblock 1) = true := by
  rw [record01_eq]
  exact dirValid_of_ok _ _ _ _ root_directory_ok

theorem dirs_valid_checked : dirsValid blockView superblock = true := by
  apply dirsValid_of_directories
  intro i member
  rw [directory_inode_list, List.mem_singleton] at member
  subst i
  exact root_dir_valid_checked

theorem root_dots_checked : dotsValid blockView 1 (dinode blockView superblock 1) = true := by
  rw [record01_eq]
  apply dotsValid_of_data_eq _ _ _ _ root_directory_data
  decide

theorem dots_all_checked : dotsAll blockView superblock = true := by
  apply dotsAll_of_directories
  intro i member
  rw [directory_inode_list, List.mem_singleton] at member
  subst i
  exact root_dots_checked

theorem root_valid_checked : rootValid blockView superblock = true :=
  rootValid_of_data_eq _ _ _ _ record01_eq root_directory_data (by decide) root_directory_dotdot

end Xv6.Fs.Image

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs." || name.toString.startsWith "Xv6.Generated.InodeW3.") then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} directory image theorem cones; standard foundational axioms only."
