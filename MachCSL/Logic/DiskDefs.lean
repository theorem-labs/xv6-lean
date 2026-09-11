import MachCSL.Devices.Virtio.Defs
import Iris.Instances.Lib.GhostMap

/-! DiskImg.v ownership at a bare runtime name. The same capacity serves a
fresh per-era image and the separate durable image whose name survives crashes. -/
namespace MachCSL.Logic.Disk
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI MachCSL.Devices.Virtio

abbrev ImageMap (V : Type) := _root_.Std.ExtTreeMap Int V
abbrev ImageRA := HeapView Int (Agree (DiscreteO Byte)) ImageMap
abbrev ImageRF := constOF ImageRA
def imageFunctor : GFunctor := ⟨ImageRF, inferInstance⟩

structure Capacity (GF : BundledGFunctors) where
  image : GhostMapG GF Int Byte ImageMap

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def mapAuth (γ : GName) (map : ImageMap Byte) : IProp GF :=
  letI := capacity.image
  ghost_map_auth γ (.own 1) map

def imageAuth (γ : GName) (disk : Devices.Virtio.Disk) : IProp GF :=
  iprop(∃ map, mapAuth capacity γ map ∗ ⌜disk_view map disk⌝)

def imageByte (γ : GName) (offset : Int) (byte : Byte) : IProp GF :=
  letI := capacity.image
  ghost_map_elem γ (.own 1) offset byte

def imageBytes (γ : GName) (offset : Int) (bytes : List Byte) : IProp GF :=
  iprop([∗list] j ↦ byte ∈ bytes, imageByte capacity γ (offset + (j : Int)) byte)

/-- Only a bound on minted keys is assumed, exactly as source disk_img_auth_sized. -/
def imageAuthSized (γ : GName) (size : Nat) (disk : Devices.Virtio.Disk) : IProp GF :=
  iprop(∃ map, mapAuth capacity γ map ∗ ⌜disk_view map disk⌝ ∗
    ⌜∀ offset byte, map[offset]? = some byte → 0 ≤ offset ∧ offset < (size : Int)⌝)

end MachCSL.Logic.Disk
