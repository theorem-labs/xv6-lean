import MachCSL.Logic.IcacheShelterDefs

namespace MachCSL.Logic.IcacheShelter
open Iris Iris.BI IcacheRefLedger IcacheSlotCoupling

structure Spec {GF : BundledGFunctors} (types : IcacheTypeGhost.Capacity GF)
    (transactions : LogTx.Capacity GF) : Prop where
  freezeNoOps : ∀ boot tx f n d, ireg_frz_ok f n d →
    iprop(⊢ LogTx.auth transactions tx ∅ -∗ ireg_fsh types transactions boot tx f -∗ ⌜f = freezeCell .off⌝)
  claimNoOps : ∀ tx c f d, ireg_claim_ok c f d →
    iprop(⊢ LogTx.auth transactions tx ∅ -∗ ireg_cpin transactions tx c -∗ ⌜c = none⌝)
  bootOff : ∀ boot tx f,
    iprop(⊢ ireg_fsh types transactions boot tx f -∗ IcacheTypeGhost.ireg_boot types boot -∗ ⌜f = freezeCell .off⌝)
  phase : ∀ boot tx ph ph', ph' = .off ∨ frz_reg ph' = frz_reg ph →
    iprop(ireg_fsh types transactions boot tx (freezeCell ph) ⊢ ireg_fsh types transactions boot tx (freezeCell ph'))
  split : ∀ boot tx c f, iprop(ireg_shp types transactions boot tx c f ⊣⊢
    ireg_fsh types transactions boot tx f ∗ ireg_cpin transactions tx c)

end MachCSL.Logic.IcacheShelter
