import Xv6.Fs.Bytes

/-! Superblock parsing and exact W1 geometry from `iris/FsImg.v:209–235,
831–909` at the pinned paper revision. Arbitrary records retain signed fields;
the decoder alone does not imply valid geometry. -/
namespace Xv6.Fs

structure Superblock where
  magic : Int
  size : Int
  nblocks : Int
  ninodes : Int
  nlog : Int
  logstart : Int
  inodestart : Int
  bmapstart : Int
  deriving DecidableEq, Repr

def parseSuperblock (image : Blocks) : Option Superblock :=
  let bytes := image 1
  if 32 ≤ bytes.length then
    some ⟨leAt bytes 0 4, leAt bytes 4 4, leAt bytes 8 4, leAt bytes 12 4,
      leAt bytes 16 4, leAt bytes 20 4, leAt bytes 24 4, leAt bytes 28 4⟩
  else none

def dataStart (sb : Superblock) : Int := sb.bmapstart + 1

def superblockValid (sb : Superblock) : Bool :=
  sb.magic == 0x10203040 && sb.logstart == 2 && sb.nlog == 31 &&
  sb.inodestart == sb.logstart + sb.nlog &&
  sb.bmapstart == sb.inodestart + (sb.ninodes / 16 + 1) &&
  sb.size == dataStart sb + sb.nblocks &&
  decide (1 < sb.ninodes) && decide (0 < sb.nblocks) &&
  decide (sb.size ≤ 8 * 1024) && decide (16 * (sb.ninodes / 16 + 1) ≤ 2 ^ 16)

structure SuperblockOK (sb : Superblock) : Prop where
  magic : sb.magic = 0x10203040
  logstart : sb.logstart = 2
  nlog : sb.nlog = 31
  inodestart : sb.inodestart = sb.logstart + sb.nlog
  bmapstart : sb.bmapstart = sb.inodestart + (sb.ninodes / 16 + 1)
  size : sb.size = dataStart sb + sb.nblocks
  ninodes : 1 < sb.ninodes
  nblocks : 0 < sb.nblocks
  oneBitmap : sb.size ≤ 8 * 1024
  ushort : 16 * (sb.ninodes / 16 + 1) ≤ 2 ^ 16

theorem superblockValid_iff (sb : Superblock) : superblockValid sb = true ↔ SuperblockOK sb := by
  simp only [superblockValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, h⟩, i⟩, j⟩
    exact ⟨a, b, c, d, e, f, g, h, i, j⟩
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h.magic, h.logstart⟩, h.nlog⟩, h.inodestart⟩, h.bmapstart⟩,
      h.size⟩, h.ninodes⟩, h.nblocks⟩, h.oneBitmap⟩, h.ushort⟩

theorem superblock_inodes_fit (sb : Superblock) (valid : SuperblockOK sb) :
    sb.inodestart + (sb.ninodes + 15) / 16 ≤ sb.bmapstart := by
  rw [valid.bmapstart]
  omega

theorem superblock_metadata (sb : Superblock) (valid : SuperblockOK sb) :
    2 < sb.inodestart ∧ sb.inodestart < dataStart sb ∧ dataStart sb ≤ sb.size := by
  obtain ⟨magic, logstart, nlog, inodestart, bmapstart, size, ninodes,
    nblocks, oneBitmap, ushort⟩ := valid
  unfold dataStart at size ⊢
  omega

theorem parseSuperblock_short (image : Blocks) (short : (image 1).length < 32) :
    parseSuperblock image = none := by
  simp [parseSuperblock, Nat.not_le.mpr short]

theorem parseSuperblock_blocks (disk : Disk) : parseSuperblock (blocks disk) =
    some ⟨leAt (blocks disk 1) 0 4, leAt (blocks disk 1) 4 4,
      leAt (blocks disk 1) 8 4, leAt (blocks disk 1) 12 4,
      leAt (blocks disk 1) 16 4, leAt (blocks disk 1) 20 4,
      leAt (blocks disk 1) 24 4, leAt (blocks disk 1) 28 4⟩ := by
  simp [parseSuperblock, blocks_length]

def logClean (image : Blocks) (sb : Superblock) : Bool :=
  MachCSL.Memory.assembleBytes ((image sb.logstart).take 4) == 0

theorem logClean_iff (image : Blocks) (sb : Superblock) : logClean image sb = true ↔
    MachCSL.Memory.assembleBytes ((image sb.logstart).take 4) = 0 := by
  simp [logClean]

theorem logClean_byte (image : Blocks) (sb : Superblock) (j : Nat)
    (clean : logClean image sb = true) (length : 4 ≤ (image sb.logstart).length)
    (bound : j < 4) : byteAt (image sb.logstart) j = 0 := by
  have h := assemble_zero_byte ((image sb.logstart).take 4) j
    ((logClean_iff image sb).mp clean) (by simp; omega)
  simpa [byteAt, List.getElem?_take, bound] using h

end Xv6.Fs
