import MachCSL.Logic.IcacheRegionSlotDefs

namespace MachCSL.Logic.IcacheRegionSlot
open Iris Iris.BI Xv6.Fs IcacheRefLedger IcacheSlotCoupling

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  intro : ∀ names view records z d c r f n,
    ireg_link_ok d → ireg_claim_ok c f d → ireg_frz_ok f n d →
    iprop(⊢ ireg_rcol capacity.reference names.reference z c r f n d -∗
      IcacheEpoch.ireg_ep capacity.epoch names.epoch z d -∗
      IcacheInodeCustody.ireg_lnk view capacity.links z d -∗
      (⌜c = none⌝ ∨ IcacheTypeGhost.ireg_open capacity.types names.boot) -∗
      IcacheCoupling.icnt_half capacity.coupling names.coupling z n -∗
      IcacheShelter.ireg_shp capacity.types capacity.transactions names.boot names.transactions c f -∗
      ireg_frzc capacity.coupling names.coupling z f -∗ arm capacity names view records z c d -∗
      ireg_slot capacity names view records z d)
  boot : ∀ names view records inum d ge gr (frame : IProp GF),
    ireg_link_ok d → (d.typeZ = 0 → IcacheInodeCustody.ireg_bare d) →
    iprop(bootInput capacity names view records inum d ge gr ∗ frame ⊢ |==>
      (ireg_slot capacity names view records inum.toNat d ∗ FsInodeRegion.out capacity.records records inum d ∗ frame))

end MachCSL.Logic.IcacheRegionSlot
