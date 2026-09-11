import MachCSL.Logic.IcacheRegionBootDefs
import MachCSL.Logic.FsBytesInvariantDefs
import MachCSL.Logic.IcacheTopRegistryDefs
import MachCSL.Logic.FsBytesGammaDefs

/-! Source inode-region invariant, preserving the actual byte and top rows. -/
namespace MachCSL.Logic.IcacheRegionInvariant
open Iris Iris.Std Iris.BI

structure Capacity (GF : BundledGFunctors) where
  region : IcacheRegionSlot.Capacity GF
  blocks : FsBlockGhost.Capacity GF
  bytes : Disk.Capacity GF
  arms : GhostMapG GF Nat IcacheTopRegistry.Entry IcacheTopRegistry.ArmMap

structure Names where
  region : IcacheRegionSlot.Names
  filesystem : FsBlocks.Names
  arms : GName

def iregN : Namespace := nroot.@("ireg" : String)
def ftopN : Namespace := nroot.@("ftop" : String)

variable {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)

def byteCapacity : FsBytesInvariant.Capacity GF := ⟨capacity.blocks, capacity.bytes⟩
def topCapacity : IcacheTopRegistry.Capacity GF :=
  ⟨capacity.arms, capacity.region.tops, capacity.region.transactions⟩
def view : FsView.View GF := FsBytesGamma.logged capacity.bytes names.filesystem
def topNames : IcacheTopRegistry.Names :=
  ⟨names.filesystem.top, names.arms, names.region.transactions⟩

/-- All source slot clients are retained through the existing concrete body.
The generic start remains independent of the epoch-name record's start. -/
def body (records : GName) (start : Int) (nib : Nat) : IProp GF :=
  IcacheRegionBoot.body capacity.region names.region (view capacity names) records start nib

variable {hlc : HasLC} [InvGS_gen hlc GF]

def topInvariant : IProp GF :=
  IcacheTopRegistry.invariant (topCapacity capacity) (topNames names) ftopN

/-- Power-on row: the byte invariant need not yet carry the empty-exception seal. -/
def ireg_reg (records : GName) (start : Int) (nib : Nat) : IProp GF :=
  iprop(inv iregN (body capacity names records start nib) ∗
    FsBytesInvariant.row (byteCapacity capacity) names.filesystem ∗ topInvariant capacity names)

/-- Post-recovery row: the seal is the actual native discarded empty-set token. -/
def ireg_inv (records : GName) (start : Int) (nib : Nat) : IProp GF :=
  iprop(inv iregN (body capacity names records start nib) ∗
    FsBytesInvariant.any (byteCapacity capacity) names.filesystem ∗ topInvariant capacity names)

end MachCSL.Logic.IcacheRegionInvariant
