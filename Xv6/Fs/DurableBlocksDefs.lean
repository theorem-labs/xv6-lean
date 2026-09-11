import Xv6.Fs.SlotsDefs
import Xv6.Fs.BitmapDefs

namespace Xv6.Fs

def entryBlocks (image : Blocks) (sb : Superblock) : List Int :=
  ((List.range sb.ninodes.toNat).map fun (i : Nat) =>
    let dn := dinode image sb (i : Int)
    if dn.typeZ == 0 then [] else inodeEntries image dn).flatten

def entrySet (image : Blocks) (sb : Superblock) : Option BlockSet :=
  collectNodup (entryBlocks image sb)

def inodeEntrySet (image : Blocks) (sb : Superblock) (i : Int) : BlockSet :=
  Std.ExtTreeSet.ofList (inodeEntries image (dinode image sb i))

end Xv6.Fs
