import Xv6.Fs.Superblock
import Xv6.Machine.Boot

/-! Checked facts about the actual mkfs disk at the paper pin. These establish
the superblock geometry and clean log, not the remaining inode/tree/bitmap
well-formedness clauses or crash consistency. Reboot does not reload this disk. -/
namespace Xv6.Fs.Image

abbrev disk : Disk := Xv6.Machine.imageDisk
abbrev blockView : Blocks := blocks disk

def superblock : Superblock := ⟨0x10203040, 2000, 1953, 200, 31, 2, 33, 46⟩

theorem parse_superblock : parseSuperblock blockView = some superblock := by
  rw [parseSuperblock_blocks]
  simp only [leAt_blocks disk 1 0 4 (by decide),
    leAt_blocks disk 1 4 4 (by decide), leAt_blocks disk 1 8 4 (by decide),
    leAt_blocks disk 1 12 4 (by decide), leAt_blocks disk 1 16 4 (by decide),
    leAt_blocks disk 1 20 4 (by decide), leAt_blocks disk 1 24 4 (by decide),
    leAt_blocks disk 1 28 4 (by decide)]
  decide

theorem superblock_valid : superblockValid superblock = true := by decide

theorem superblock_ok : SuperblockOK superblock :=
  (superblockValid_iff superblock).mp superblock_valid

theorem log_clean : logClean blockView superblock = true := by
  unfold logClean
  change (MachCSL.Memory.assembleBytes ((blocks disk 2).take 4) == 0) = true
  have take : (blocks disk 2).take 4 =
      [disk 2048, disk 2049, disk 2050, disk 2051] := by
    unfold blocks
    rw [← List.map_take, List.take_range]
    rfl
  rw [take]
  decide

theorem log_header_zero (j : Nat) (bound : j < 4) : byteAt (blockView 2) j = 0 :=
  logClean_byte blockView superblock j log_clean (by rw [blocks_length]; decide) bound

theorem blocks_full (block : Int) : (blockView block).length = 1024 := blocks_length disk block

/-- Concrete rejection witness: change one byte of the input superblock. -/
def badMagicDisk : Disk := fun address => if address = 1024 then 0 else disk address

theorem bad_magic_parse : parseSuperblock (blocks badMagicDisk) =
    some { superblock with magic := 0x10203000 } := by
  rw [parseSuperblock_blocks]
  simp only [leAt_blocks badMagicDisk 1 0 4 (by decide),
    leAt_blocks badMagicDisk 1 4 4 (by decide), leAt_blocks badMagicDisk 1 8 4 (by decide),
    leAt_blocks badMagicDisk 1 12 4 (by decide), leAt_blocks badMagicDisk 1 16 4 (by decide),
    leAt_blocks badMagicDisk 1 20 4 (by decide), leAt_blocks badMagicDisk 1 24 4 (by decide),
    leAt_blocks badMagicDisk 1 28 4 (by decide)]
  decide

theorem bad_magic_rejected :
    (parseSuperblock (blocks badMagicDisk)).map superblockValid = some false := by
  rw [bad_magic_parse]
  decide

end Xv6.Fs.Image
