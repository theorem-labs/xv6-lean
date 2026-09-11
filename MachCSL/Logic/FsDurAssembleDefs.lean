import MachCSL.Logic.FsDurAllocDefs
import MachCSL.Logic.FsStateDefs

/-! The residual byte column of the source footprint assembly. This names
an exact map difference; it does not introduce another filesystem carrier. -/
namespace MachCSL.Logic.FsDurAssemble
open Iris Iris.Std Iris.BI Xv6.Fs DurableState

def remainderMap (whole : FsDurBytes.ByteMap) (state : State) (disk : BlockMap) : FsDurBytes.ByteMap :=
  PartialMap.difference (M := Disk.ImageMap) whole
    (FsDurAlloc.selected (FsDurAlloc.family state) (FsDurAlloc.fpMap state disk))

def remainder {GF : BundledGFunctors} (view : FsView.View GF)
    (whole : FsDurBytes.ByteMap) (state : State) (disk : BlockMap) : IProp GF :=
  FsDurBytes.byteLedger view (remainderMap whole state disk)

end MachCSL.Logic.FsDurAssemble
