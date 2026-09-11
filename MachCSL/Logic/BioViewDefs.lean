import MachCSL.Logic.DiskClientDefs
import Xv6.Fs.SnapshotHomeDefs

/-! Complete source BioDefs.bio_view and BioInv.pool_blk. No Bio invariant
is assumed by this client carrier or its existential block ownership. -/
namespace MachCSL.Logic.BioView
open Iris Iris.BI MachCSL.Memory

structure View (GF : BundledGFunctors) where
  names : DiskClient.Names
  device : BitVec 32
  covered : Xv6.Fs.BlockSet
  clean : Int → List Byte → IProp GF
  dirty : Int → List Byte → IProp GF
  cleanTimeless : ∀ b bytes, Timeless (clean b bytes)
  dirtyTimeless : ∀ b bytes, Timeless (dirty b bytes)

variable {GF : BundledGFunctors}

def poolBlock (capacity : Disk.Capacity GF) (view : View GF) (b : Int) : IProp GF :=
  iprop(∃ bytes : List Byte, DiskClient.diskBlock capacity view.names b bytes ∗ view.clean b bytes)

end MachCSL.Logic.BioView
