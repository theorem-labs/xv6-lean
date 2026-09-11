import MachCSL.Logic.FsBytesGammaDefs
import MachCSL.Logic.FsStateBitmapDefs
import Xv6.Fs.SnapshotConfigDefs

/-! BitmapInv.bitmap_res is exactly free_bitmap_at at the logged view.
It carries the bitmap's bytes and the native free pool, with no pure coverage clause. -/
namespace MachCSL.Logic.FsBitmap
open Iris Xv6.Fs
variable {GF : BundledGFunctors}

def resource (dc : Disk.Capacity GF) (names : FsBlocks.Names) (bitmapBlock size : Int) (used : BlockSet) : IProp GF :=
  FsState.freeBitmapAt (FsBytesGamma.logged dc names) bitmapBlock size used

end MachCSL.Logic.FsBitmap
