import MachCSL.Logic.IcacheRegionSlotDefs
import MachCSL.Logic.FsInodeRegionBytesDefs

/-! Exact finite inode blocks and covered native registry before invariant allocation. -/
namespace MachCSL.Logic.IcacheRegionBoot
open Iris Iris.Std Iris.BI Xv6.Fs SnapshotConfig IcacheRefLedger
abbrev Capacity := IcacheRegionSlot.Capacity
abbrev Names := IcacheRegionSlot.Names

def dummyRegistry (nib : Nat) : IcacheEscrowTokens.TokenMap IcacheEscrowTokens.RegistryValue :=
  FiniteMap.ofSetWith (M := IcacheEscrowTokens.TokenMap) (fun _ => (1, 1)) (regionInums nib)

variable {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)
    (view : FsView.View GF) (records : GName)

def block (start : Int) (map : FsInodeRegion.RecordMap Dinode) (bi : Nat) : IProp GF :=
  iprop(∃ ds, ⌜InodeBlockWellFormed ds⌝ ∗ ⌜FsInodeRegion.couple map bi ds⌝ ∗
    FsInodeRegion.recs view start bi ds ∗
    [∗list] i ∈ List.range 16, IcacheRegionSlot.ireg_slot capacity names view records
      (16 * (bi : Int) + ((i : Nat) : Int)) (ds[i]?.getD default))

def coveredRegistry (nib : Nat) : IProp GF :=
  iprop(∃ map : IcacheEscrowTokens.TokenMap IcacheEscrowTokens.RegistryValue,
    ⌜∀ z : Int, 0 ≤ z ∧ z < 16 * (nib : Int) → (map[z]?).isSome⌝ ∗
    IcacheEscrowTokens.reg_auth capacity.escrow names.registry map)

def body (start : Int) (nib : Nat) : IProp GF :=
  iprop(∃ map : FsInodeRegion.RecordMap Dinode, FsInodeRegion.auth capacity.records records map ∗
    ([∗list] bi ∈ List.range nib, block capacity names view records start map bi) ∗
    coveredRegistry capacity names nib)

def slots (dss : List (List Dinode)) (nib : Nat) : IProp GF :=
  bigSepS (fun z => IcacheRegionSlot.ireg_slot capacity names view records z
    (InodeRegionImage.imageDinode dss z)) (regionInums nib)

def outside (dss : List (List Dinode)) (nib : Nat) : IProp GF :=
  bigSepS (fun z => FsInodeRegion.out capacity.records records (BitVec.ofInt 32 z)
    (InodeRegionImage.imageDinode dss z)) (regionInums nib)

def registryRows (nib : Nat) : IProp GF :=
  bigSepS (fun z => IcacheEscrowTokens.reg_full capacity.escrow names.registry z 1 1) (regionInums nib)

/-- The six native client columns, bundled pointwise for distribution.
They are inputs, not consequences of a pure image validity proof. -/
def clients (nib : Nat) (counts : Int → Nat) (imageRecords : Int → Dinode) : IProp GF :=
  bigSepS (fun z => iprop(
    link_auth capacity.reference names.reference z none 0 (freezeCell .off) 0 ∗
    LogEpoch.epochAuth capacity.epoch (names.epoch.observation z) 0 ∗
    IcacheCoupling.icnt_half capacity.coupling names.coupling z 0 ∗
    IcacheCoupling.frzm_h capacity.coupling names.coupling z false ∗
    IcacheInodeCustody.ireg_lnk_at view capacity.links z (counts z) (imageRecords z).typeZ ∗
    IcacheRegionSlot.topBoot capacity view z (imageRecords z))) (regionInums nib)

end MachCSL.Logic.IcacheRegionBoot
