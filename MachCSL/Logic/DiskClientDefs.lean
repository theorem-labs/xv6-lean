import MachCSL.Logic.DiskDefs
import MachCSL.Memory.Defs

/-! The complete DiskPtsto.disk_names carrier and its image-camera resource
projections. Driver protocol ownership and allocation are separate. -/
namespace MachCSL.Logic.DiskClient
open Iris Iris.BI MachCSL.Memory

structure Names where
  img : GName
  slot : GName
  nc : GName
  np : GName
  claim : GName
  cfg : GName
  ord : GName
  nr : GName
  stage : GName
  head : GName
  perm : GName
  fl0 : GName
  fl1 : GName
  flr : GName
  pos : GName

variable {GF : BundledGFunctors} (capacity : Disk.Capacity GF)

def diskByte (names : Names) (offset : Int) (byte : Byte) : IProp GF :=
  Disk.imageByte capacity names.img offset byte

def diskBytes (names : Names) (offset : Int) (bytes : List Byte) : IProp GF :=
  Disk.imageBytes capacity names.img offset bytes

def diskBlock (names : Names) (block : Int) (bytes : List Byte) : IProp GF :=
  iprop(⌜bytes.length = 1024⌝ ∗ diskBytes capacity names (block * 1024) bytes)

end MachCSL.Logic.DiskClient
