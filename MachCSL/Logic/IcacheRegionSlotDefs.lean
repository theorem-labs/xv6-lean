import MachCSL.Logic.IcacheInodeCustodyDefs
import MachCSL.Logic.IcacheEpochDefs
import MachCSL.Logic.IcacheEscrowTokensDefs
import MachCSL.Logic.IcacheShelterDefs
import MachCSL.Logic.FsInodeRegionDefs

/-! Complete source inode slot, retaining all native columns and both arms. -/
namespace MachCSL.Logic.IcacheRegionSlot
open Iris Iris.BI Xv6.Fs IcacheRefLedger IcacheSlotCoupling

def ireg_in (c : ClaimCell) (d : Dinode) : Prop :=
  d.typeZ = 0 ∨ (fresh_shape d ∧ c ≠ none)
def ireg_marked_ok (c : ClaimCell) (d : Dinode) : Prop := d.typeZ ≠ 0 ∧ c = none
abbrev ireg_ty_ok := InodeRegionImage.typeOK

def ireg_link_ok (d : Dinode) : Prop :=
  (d.typeZ = 0 → d.nlinkZ = 0) ∧ d.nlinkZ ≤ 32767 ∧ ireg_ty_ok d

structure Capacity (GF : BundledGFunctors) where
  reference : IcacheRefLedger.Capacity GF
  coupling : IcacheCoupling.Capacity GF
  types : IcacheTypeGhost.Capacity GF
  transactions : LogTx.Capacity GF
  records : FsInodeRegion.Capacity GF
  links : FsLink.Capacity GF
  tops : FsTop.Capacity GF
  epoch : LogEpoch.Capacity GF
  escrow : IcacheEscrowTokens.Capacity GF

structure Names where
  reference : GName
  coupling : IcacheCoupling.Names
  boot : GName
  transactions : GName
  registry : GName
  epoch : IcacheEpoch.Names

variable {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)
    (view : FsView.View GF) (records : GName)

/-- The two existential registry halves in the pending branch remain separate;
native agreement, not the definition, identifies their escrow-name pairs. -/
def arm (z : Int) (c : ClaimCell) (d : Dinode) : IProp GF :=
  iprop(((((⌜ireg_in c d⌝ ∗ FsInodeRegion.frag capacity.records records z d ∗
      IcacheInodeCustody.ireg_top_park view capacity.tops z d) ∨
    (⌜ireg_marked_ok c d⌝ ∗ FsInodeRegion.imark capacity.records records z)) ∗
    (∃ ge gr, IcacheEscrowTokens.reg_full capacity.escrow names.registry z ge gr))) ∨
    (⌜d.typeZ = 0⌝ ∗ FsInodeRegion.frag capacity.records records z d ∗
      (∃ ge gr, IcacheEscrowTokens.reg_half capacity.escrow names.registry z ge gr) ∗
      IcacheEscrowTokens.region_pending capacity.escrow names.registry z ∗
      IcacheInodeCustody.ireg_top_park view capacity.tops z d))

def ireg_slot (z : Int) (d : Dinode) : IProp GF :=
  iprop((∃ (r : Nat) (c : ClaimCell) (f : FreezeCell) (n : Nat),
    ireg_rcol capacity.reference names.reference z c r f n d ∗
    ⌜ireg_link_ok d⌝ ∗ (⌜c = none⌝ ∨ IcacheTypeGhost.ireg_open capacity.types names.boot) ∗
    IcacheCoupling.icnt_half capacity.coupling names.coupling z n ∗
    ⌜ireg_claim_ok c f d⌝ ∗ ⌜ireg_frz_ok f n d⌝ ∗
    IcacheShelter.ireg_shp capacity.types capacity.transactions names.boot names.transactions c f ∗
    ireg_frzc capacity.coupling names.coupling z f ∗ arm capacity names view records z c d) ∗
    IcacheEpoch.ireg_ep capacity.epoch names.epoch z d ∗
    IcacheInodeCustody.ireg_lnk view capacity.links z d)

def topBoot (z : Int) (d : Dinode) : IProp GF :=
  if d.typeZ = 0 then FsTop.topFrag capacity.tops view z (IcacheInodeCustody.freeNode d) else emp

/-- All supplied pointwise boot resources, with the observation counter still
at zero. This predicate allocates nothing and imposes no extra image facts. -/
def bootInput (inum : BitVec 32) (d : Dinode) (ge gr : GName) : IProp GF :=
  let z : Int := inum.toNat
  iprop(FsInodeRegion.dinodeAt capacity.records records inum d ∗
    FsInodeRegion.imark capacity.records records z ∗
    link_auth capacity.reference names.reference z none 0 (freezeCell .off) 0 ∗
    LogEpoch.epochAuth capacity.epoch (names.epoch.observation z) 0 ∗
    IcacheEscrowTokens.reg_full capacity.escrow names.registry z ge gr ∗
    IcacheCoupling.icnt_half capacity.coupling names.coupling z 0 ∗
    IcacheCoupling.frzm_h capacity.coupling names.coupling z false ∗
    IcacheInodeCustody.ireg_lnk view capacity.links z d ∗ topBoot capacity view z d)

end MachCSL.Logic.IcacheRegionSlot
