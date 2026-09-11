import MachCSL.Logic.DiskDefs
import MachCSL.Memory.Defs

/-! Fraction-indexed filesystem views, source `FsStateDefs.v`. The byte
predicate is a parameter here; `FsViewLink` supplies the actual disk camera. -/
namespace MachCSL.Logic.FsView
open Iris Iris.Std Iris.BI MachCSL.Memory

structure View (GF : BundledGFunctors) where
  phi : DFrac → Int → Byte → IProp GF
  link : GName
  top : GName

variable {GF : BundledGFunctors}

def byteRangeQ (view : View GF) (dq : DFrac) (block offset : Int) (bytes : List Byte) : IProp GF :=
  iprop([∗list] k ↦ byte ∈ bytes, view.phi dq (block * 1024 + offset + (k : Int)) byte)

def byteRange (view : View GF) (block offset : Int) (bytes : List Byte) : IProp GF :=
  byteRangeQ view (.own 1) block offset bytes

def blockOwnedQ (view : View GF) (dq : DFrac) (block : Int) (bytes : List Byte) : IProp GF :=
  iprop(⌜bytes.length = 1024⌝ ∗ byteRangeQ view dq block 0 bytes)

def blockOwned (view : View GF) (block : Int) (bytes : List Byte) : IProp GF :=
  iprop(⌜bytes.length = 1024⌝ ∗ byteRange view block 0 bytes)

/-- The byte share is fixed; ghost names are copied unchanged. This operation
does not preserve the source's fraction-indexed exclusivity law. -/
def gammaQ (view : View GF) (dq : DFrac) : View GF :=
  ⟨fun _ a byte => view.phi dq a byte, view.link, view.top⟩

end MachCSL.Logic.FsView
