import Xv6.Fs.TreeDiskProofs
import Xv6.Fs.ValidityImage

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Xv6.Fs.Image
open Xv6.Generated.InodeW3

abbrev initialTree : FsTree := treeOfDisk blockView superblock

theorem initial_tree_wf : TreeWellFormed initialTree :=
  fsimgValid_tree_wf blockView superblock fsimg_valid_checked

theorem initial_root_path (name : FName) : pathAt initialTree 1 [name] =
    (dirFirst rootDirectoryData 64 name).map (fun k => ((dirInum rootDirectoryData k).toNat : Int)) := by
  rw [pathAt_disk_dir blockView superblock 1 name (by decide)
    (rootValid_type blockView superblock root_valid_checked)]
  simp only [fileData, record01_eq, root_directory_data]
  rfl

theorem initial_echo_path : pathAt initialTree 1 [[101,99,104,111]] = some 4 := by
  rw [initial_root_path]
  decide

theorem initial_init_path : pathAt initialTree 1 [[105,110,105,116]] = some 7 := by
  rw [initial_root_path]
  decide

theorem initial_sh_path : pathAt initialTree 1 [[115,104]] = some 13 := by
  rw [initial_root_path]
  decide

theorem initial_sync_path : pathAt initialTree 1 [[115,121,110,99]] = some 22 := by
  rw [initial_root_path]
  decide

theorem initial_dot_path : pathAt initialTree 1 [dotName] = some 1 := by
  rw [initial_root_path]
  decide

theorem initial_dotdot_path : pathAt initialTree 1 [dotdotName] = some 1 := by
  rw [initial_root_path]
  decide

theorem initial_missing_name : pathAt initialTree 1 [[255]] = none := by
  rw [initial_root_path]
  decide

end Xv6.Fs.Image

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, info) in (← getEnv).constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs." || name.toString.startsWith "Xv6.Generated.InodeW3.") then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} filesystem tree theorem cones; standard foundational axioms only."
