import MachCSL.Logic.IcacheInodeCustodyDefs

namespace MachCSL.Logic.IcacheInodeCustody
open Iris Iris.BI Xv6.Fs

structure Spec {GF : BundledGFunctors} (links : FsLink.Capacity GF)
    (tops : FsTop.Capacity GF) : Prop where
  retype : ∀ view z d d', d.nlinkZ = 0 → d'.nlinkZ = 0 →
    iprop(ireg_lnk view links z d ⊢ ireg_lnk view links z d')
  bump : ∀ view z d d' k, ireg_mult d' = ireg_mult d + k → d'.typeZ = d.typeZ →
    iprop(⊢ ireg_lnk view links z d ==∗ ireg_lnk view links z d' ∗
      ∃ v, ⌜ireg_reg_ok d.typeZ v⌝ ∗ FsLink.toks links view.link z (FsLink.reps k v))
  drop : ∀ view z d d' v k, ireg_mult d = ireg_mult d' + k → d'.typeZ = d.typeZ →
    iprop(⊢ ireg_lnk view links z d -∗ FsLink.toks links view.link z (FsLink.reps k v) ==∗
      ireg_lnk view links z d')
  root : ∀ view d, iprop(ireg_lnk view links 1 d ⊢ ⌜1 ≤ d.nlinkZ⌝)
  topOpen : ∀ view z d, d.typeZ = 0 →
    iprop(ireg_top_park view tops z d ⊢ ⌜ireg_bare d⌝ ∗ FsTop.topFrag tops view z (freeNode d))

end MachCSL.Logic.IcacheInodeCustody
