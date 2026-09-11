import MachCSL.Logic.FsBytesGammaDefs
import MachCSL.Logic.FsDurXferRunsProofs

namespace MachCSL.Logic.FsBytesGamma
open Iris Iris.Std Iris.CMRA Iris.BI MachCSL.Memory
variable {GF : BundledGFunctors} (capacity : Disk.Capacity GF) (names : FsBlocks.Names)

theorem phi (dq : DFrac) (a : Int) (v : Byte) :
    (logged capacity names).phi dq a v = FsBlocks.byteElem capacity names.bytes dq a v := rfl

theorem names_eq : (logged capacity names).link = names.link ∧
    (logged capacity names).top = names.top := ⟨rfl, rfl⟩

theorem logged_snapGamma : logged capacity names =
    FsView.snapGamma capacity names.bytes names.link names.top := rfl

theorem exclusive : FsView.PhiExcl (logged capacity names) :=
  FsView.snapGamma_excl capacity names.bytes names.link names.top

theorem fractional : FsView.PhiFrac (logged capacity names) :=
  FsView.snapGamma_frac capacity names.bytes names.link names.top

instance timeless : FsView.GTimeless (logged capacity names) :=
  FsView.snapGamma_timeless capacity names.bytes names.link names.top

theorem byteRange (b off : Int) (bytes : List Byte) :
    FsView.byteRange (logged capacity names) b off bytes ⊣⊢
      FsBlocks.byteRange capacity names.bytes b off bytes := .rfl

theorem block (b : Int) (bytes : List Byte) :
    FsView.blockOwned (logged capacity names) b bytes ⊣⊢
      FsBlocks.block capacity names.bytes b bytes := .rfl

theorem byteRangeQ (dq : DFrac) (b off : Int) (bytes : List Byte) :
    FsView.byteRangeQ (logged capacity names) dq b off bytes ⊣⊢
      FsBlocks.byteRangeQ capacity names.bytes dq b off bytes := .rfl

theorem blockQ (dq : DFrac) (b : Int) (bytes : List Byte) :
    FsView.blockOwnedQ (logged capacity names) dq b bytes ⊣⊢
      FsBlocks.blockQ capacity names.bytes dq b bytes := .rfl

/-- The logged byte authority is a legal source for resource transfer, with
no assertion here that its map equals RAM, cache contents or durable media. -/
theorem agree (map : Disk.ImageMap Byte) :
    FsDurXferRuns.PhiAgree (logged capacity names) (Disk.mapAuth capacity names.bytes map) map :=
  FsDurXferRuns.snap_gamma_agree capacity names.bytes names.link names.top map

theorem registry_slot : FsLink.eraCapacity.disk.image.elem.τ = 12 := rfl

end MachCSL.Logic.FsBytesGamma
