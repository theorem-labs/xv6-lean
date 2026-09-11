import Xv6.Fs.BitmapDefs

namespace Xv6.Fs

def BitmapOK (image : Blocks) (sb : Superblock) (used : BlockSet) : Prop :=
  ∀ b : Int, 0 ≤ b ∧ b < sb.size →
    (bitmapBit (image sb.bmapstart) b = true ↔ b < dataStart sb ∨ b ∈ used)

def BlocksBitmapOK (image : Blocks) (sb : Superblock) : Prop :=
  ∃ used : BlockSet, usedSet image sb = some used ∧
    (usedBlocks image sb).Nodup ∧ BitmapOK image sb used

end Xv6.Fs
