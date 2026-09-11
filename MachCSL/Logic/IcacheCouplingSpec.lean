import MachCSL.Logic.IcacheCouplingDefs

namespace MachCSL.Logic.IcacheCoupling
open Iris Iris.BI
variable {GF : BundledGFunctors}

structure Spec (capacity : Capacity GF) : Prop where
  countAgree : ∀ names i n m, iprop(icnt_half capacity names i n ∗ icnt_half capacity names i m ⊢ ⌜n = m⌝)
  countUpdate : ∀ names i n m, iprop(icnt_half capacity names i n ∗ icnt_half capacity names i n ⊢
    |==> (icnt_half capacity names i m ∗ icnt_half capacity names i m))
  mirrorAgree : ∀ names i b b', iprop(frzm_h capacity names i b ∗ frzm_h capacity names i b' ⊢ ⌜b = b'⌝)
  mirrorUpdate : ∀ names i b b', iprop(frzm_h capacity names i b ∗ frzm_h capacity names i b ⊢
    |==> (frzm_h capacity names i b' ∗ frzm_h capacity names i b'))
  pinAgree : ∀ names k v v', iprop(hpn_h capacity names k v ∗ hpn_h capacity names k v' ⊢ ⌜v = v'⌝)
  pinUpdate : ∀ names k v v', iprop(hpn_full capacity names k v ⊢ |==> hpn_full capacity names k v')
  countBoot : ∀ names inums, countMapOwned capacity names inums ⊢ bootCounts capacity names inums
  mirrorBoot : ∀ names inums, mirrorMapOwned capacity names inums ⊢ bootMirrors capacity names inums
  pinBoot : ∀ names, pinMapOwned capacity names ⊢ bootPins capacity names
  allocate : ∀ inums (frame : IProp GF), iprop(frame ⊢ |==> ∃ names,
    bootCounts capacity names inums ∗ bootMirrors capacity names inums ∗ bootPins capacity names ∗ frame)

end MachCSL.Logic.IcacheCoupling
