import MachCSL.Logic.DiskDefs
import MachCSL.Memory.Defs

namespace MachCSL.Logic.FsBlocks
open Iris Iris.Std Iris.BI MachCSL.Memory

/-- All six source FsBlocks.fs_names fields. Allocation and invariant
ownership are separate; no ghost name here stands for an assumed resource. -/
structure Names where
  cache : GName
  dirty : GName
  bytes : GName
  link : GName
  top : GName
  exceptions : GName

variable {GF : BundledGFunctors} (capacity : Disk.Capacity GF)

/-- The logged view uses the existing signed disk-byte camera at its own name. -/
def byteElem (g : GName) (dq : DFrac) (a : Int) (v : Byte) : IProp GF :=
  letI := capacity.image
  ghost_map_elem g dq a v

def byteRangeQ (g : GName) (dq : DFrac) (block offset : Int) (bytes : List Byte) : IProp GF :=
  iprop([∗list] k ↦ byte ∈ bytes, byteElem capacity g dq (block * 1024 + offset + (k : Int)) byte)

def byteRange (g : GName) (block offset : Int) (bytes : List Byte) : IProp GF :=
  byteRangeQ capacity g (.own 1) block offset bytes

def blockQ (g : GName) (dq : DFrac) (block : Int) (bytes : List Byte) : IProp GF :=
  iprop(⌜bytes.length = 1024⌝ ∗ byteRangeQ capacity g dq block 0 bytes)

def block (g : GName) (b : Int) (bytes : List Byte) : IProp GF :=
  blockQ capacity g (.own 1) b bytes

end MachCSL.Logic.FsBlocks
