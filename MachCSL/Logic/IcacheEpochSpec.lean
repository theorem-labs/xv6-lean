import MachCSL.Logic.IcacheEpochDefs

namespace MachCSL.Logic.IcacheEpoch
open Iris Iris.BI Xv6.Fs Xv6.Fs.SnapshotConfig

structure Spec {GF : BundledGFunctors} (capacity : LogEpoch.Capacity GF) : Prop where
  init : ∀ names inum record, iprop(⊢ LogEpoch.epochAuth capacity (names.observation inum) 0 ==∗
    ireg_ep capacity names inum record)
  mint : ∀ names inum record epoch, record.nlink.toNat ≠ 0 →
    iprop(⊢ ireg_ep capacity names inum record -∗ LogEpoch.log_epoch_lb capacity names.logEpoch epoch ==∗
      ireg_ep capacity names inum record ∗ nlz_obs capacity names inum epoch)
  use : ∀ names inum record epoch, record.nlink.toNat = 0 → 1 ≤ epoch →
    iprop(⊢ ireg_ep capacity names inum record -∗ nlz_obs capacity names inum epoch -∗
      ireg_ep capacity names inum record ∗ ∃ logged : Nat, ⌜epoch ≤ logged⌝ ∗
        LogEpoch.logged_at capacity names.logged logged (iblkOf names inum))
  deposit : ∀ names inum record, iprop(⊢ ireg_ep capacity names inum record -∗
    ∃ value : Nat, LogEpoch.log_epoch_lb capacity names.logEpoch value ∗
      ∀ record' : Dinode, izrcpt capacity names inum record' value -∗ ireg_ep capacity names inum record')

end MachCSL.Logic.IcacheEpoch
