import Xv6.Fs.TreeDiskImage
import Xv6.Generated.User.EchoEncoding
import Xv6.Generated.User.InitEncoding
import Xv6.Generated.User.ShEncoding
import Xv6.Generated.User.SyncEncoding
import Xv6.Generated.User.EchoDisk
import Xv6.Generated.User.InitDisk
import Xv6.Generated.User.ShDisk
import Xv6.Generated.User.SyncDisk

namespace Xv6.Fs.Image
open Xv6.Generated.User Xv6.Generated.InodeW3

theorem echo_node : nodeAt blockView superblock 4 = some (.file (packedFileBytes echoPacked)) :=
  nodeAt_of_file_content blockView superblock 4 record04 _ record04_eq (by decide) (by decide) echoFileBytes

theorem init_node : nodeAt blockView superblock 7 = some (.file (packedFileBytes initPacked)) :=
  nodeAt_of_file_content blockView superblock 7 record07 _ record07_eq (by decide) (by decide) initFileBytes

theorem sh_node : nodeAt blockView superblock 13 = some (.file (packedFileBytes shPacked)) :=
  nodeAt_of_file_content blockView superblock 13 record13 _ record13_eq (by decide) (by decide) shFileBytes

theorem sync_node : nodeAt blockView superblock 22 = some (.file (packedFileBytes syncPacked)) :=
  nodeAt_of_file_content blockView superblock 22 record22 _ record22_eq (by decide) (by decide) syncFileBytes

/-- Source raw hex decoding, root path, and exact file-content node in one statement. -/
theorem echo_file :
    Xv6.Image.decodeChunks echoHexChunks = some (ByteArray.mk echoPacked.toBytes.toArray) ∧
    pathAt initialTree 1 [[101,99,104,111]] = some 4 ∧
    initialTree.nodes[(4 : Int)]? = some (.file (packedFileBytes echoPacked)) := by
  refine ⟨echo_decode_eq, initial_echo_path, ?_⟩
  rw [treeOfDisk_lookup blockView superblock 4 (by decide)]
  exact echo_node

theorem init_file :
    Xv6.Image.decodeChunks initHexChunks = some (ByteArray.mk initPacked.toBytes.toArray) ∧
    pathAt initialTree 1 [[105,110,105,116]] = some 7 ∧
    initialTree.nodes[(7 : Int)]? = some (.file (packedFileBytes initPacked)) := by
  refine ⟨init_decode_eq, initial_init_path, ?_⟩
  rw [treeOfDisk_lookup blockView superblock 7 (by decide)]
  exact init_node

theorem sh_file :
    Xv6.Image.decodeChunks shHexChunks = some (ByteArray.mk shPacked.toBytes.toArray) ∧
    pathAt initialTree 1 [[115,104]] = some 13 ∧
    initialTree.nodes[(13 : Int)]? = some (.file (packedFileBytes shPacked)) := by
  refine ⟨sh_decode_eq, initial_sh_path, ?_⟩
  rw [treeOfDisk_lookup blockView superblock 13 (by decide)]
  exact sh_node

theorem sync_file :
    Xv6.Image.decodeChunks syncHexChunks = some (ByteArray.mk syncPacked.toBytes.toArray) ∧
    pathAt initialTree 1 [[115,121,110,99]] = some 22 ∧
    initialTree.nodes[(22 : Int)]? = some (.file (packedFileBytes syncPacked)) := by
  refine ⟨sync_decode_eq, initial_sync_path, ?_⟩
  rw [treeOfDisk_lookup blockView superblock 22 (by decide)]
  exact sync_node

end Xv6.Fs.Image

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, info) in (← getEnv).constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs." || name.toString.startsWith "Xv6.Generated.User." ||
        name.toString.startsWith "Xv6.Generated.InodeW3.") then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} independent user-ELF/file-content theorem cones; standard foundational axioms only."
