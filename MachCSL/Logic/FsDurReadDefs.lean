import MachCSL.Logic.FsDurBytesDefs
import MachCSL.Logic.FsViewLink
import MachCSL.Logic.FsStateBitmapDefs

/-! FsDurRead.v's block-width condition and exact nonempty run-reading result.
The full-width condition belongs to the committed block map's caller; it is
not inferred from the native snapshot's single Shape condition. -/
namespace MachCSL.Logic.FsDurRead
open Xv6.Fs DurableState

abbrev BlocksFull := FsDurBytes.BlocksFull

def RunSlice (disk : BlockMap) (block offset : Int) (bytes : List (BitVec 8)) : Prop :=
  ∃ stored, disk[block]? = some stored ∧ stored.length = 1024 ∧
    ∃ pre post, stored = pre ++ bytes ++ post ∧ (pre.length : Int) = offset

end MachCSL.Logic.FsDurRead
