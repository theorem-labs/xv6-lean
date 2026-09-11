import MachCSL.Logic.FsInodeRegionDefs
import MachCSL.Logic.FsInodeRegionCodecDefs

namespace MachCSL.Logic.FsInodeRegion
open Iris Iris.Std Iris.BI Xv6.Fs MachCSL.Memory
variable {GF : BundledGFunctors}

def regionBytes (view : FsView.View GF) (start : Int) (blocks : List (List Byte)) : IProp GF :=
  bigSepL (fun bi bytes => FsView.blockOwned view (start + (bi : Int)) bytes) blocks

def regionRecs (view : FsView.View GF) (start : Int) (records : List (List Dinode)) : IProp GF :=
  bigSepL (fun bi ds => recs view start bi ds) records

def Decoded (blocks : List (List Byte)) (records : List (List Dinode)) : Prop :=
  records.length = blocks.length ∧
  (∀ ds ∈ records, InodeBlockWellFormed ds) ∧
  ∀ bi : Nat, bi < blocks.length → blocks[bi]?.getD [] = inodeBlockBytes (records[bi]?.getD [])

end MachCSL.Logic.FsInodeRegion
