import MachCSL.Logic.IcacheRegionBootDefs

namespace MachCSL.Logic.IcacheRegionBoot
open Iris Iris.BI Xv6.Fs

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  bootstrap : ∀ names view start blocks counts imageRecords (frame : IProp GF),
    (∀ block ∈ blocks, block.length = 1024) →
    16 * (blocks.length : Int) ≤ 2 ^ 32 →
    (∀ dss, FsInodeRegion.Decoded blocks dss →
      InodeRegionImage.Premises dss blocks.length counts imageRecords) →
    iprop(FsInodeRegion.regionBytes view start blocks ∗ clients capacity names view blocks.length counts imageRecords ∗
      IcacheEscrowTokens.reg_auth capacity.escrow names.registry ∅ ∗ frame ⊢ |==> ∃ records dss,
      ⌜FsInodeRegion.Decoded blocks dss ∧ InodeRegionImage.Premises dss blocks.length counts imageRecords⌝ ∗
      body capacity names view records start blocks.length ∗ outside capacity records dss blocks.length ∗ frame)

end MachCSL.Logic.IcacheRegionBoot
