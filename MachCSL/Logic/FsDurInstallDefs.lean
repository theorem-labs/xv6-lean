import MachCSL.Logic.FsDurXferShapeDefs

/-! Source FsDurXfer installation uses the existing byte family and returns
exactly the map difference. These facts are read from source ownership later. -/
namespace MachCSL.Logic.FsDurInstall
open Iris Iris.Std Iris.BI Xv6.Fs DurableState FsDurXferRuns

structure Facts (state : State) (pool : BlockMap) (whole : FsDurBytes.ByteMap) : Prop where
  shape : FsDurXferShape.Shape state pool
  disjoint : RunsDisjoint (FsDurXferShape.fsRuns state pool)
  included : PartialMap.submap (M := Disk.ImageMap) (runUnion (FsDurXferShape.fsRuns state pool)) whole

def remainder (state : State) (pool : BlockMap) (whole : FsDurBytes.ByteMap) : FsDurBytes.ByteMap :=
  PartialMap.difference (M := Disk.ImageMap) whole (runUnion (FsDurXferShape.fsRuns state pool))

end MachCSL.Logic.FsDurInstall
