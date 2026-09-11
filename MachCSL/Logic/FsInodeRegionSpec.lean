import MachCSL.Logic.FsInodeRegionDefs

namespace MachCSL.Logic.FsInodeRegion
open Iris Iris.Std Iris.BI Xv6.Fs
variable {GF : BundledGFunctors}

structure Spec (capacity : Capacity GF) : Prop where
  lookup : ∀ g records dq i record, iprop(auth capacity g records ∗ fragQ capacity g dq i record ⊢ ⌜records[i]? = some record⌝)
  markerExclusive : ∀ g i, iprop(imark capacity g i ∗ imark capacity g i ⊢ False)
  allocate : ∀ records, iprop(⊢ |==> ∃ g, auth capacity g records ∗ allFragments capacity g records)
  boot : ∀ records (nib : Nat), 16 * (nib : Int) ≤ 2 ^ 32 → ∀ frame : IProp GF,
    iprop(frame ⊢ |==> ∃ g, auth capacity g (initialMap records nib) ∗ bootCells capacity g records nib ∗ frame)

end MachCSL.Logic.FsInodeRegion
