import MachCSL.Logic.IcacheEpochSpec
import MachCSL.Logic.LogEpochProofs

namespace MachCSL.Logic.IcacheEpoch
open Iris Iris.BI Xv6.Fs Xv6.Fs.SnapshotConfig
variable {GF : BundledGFunctors} (capacity : LogEpoch.Capacity GF) (names : Names)

theorem iblkOf_inum (inum : BitVec 32) :
    iblkOf names inum.toNat = Xv6.Fs.inodeBlock inum names.inodeStart := rfl

instance izrcpt_timeless inum record value : Timeless (izrcpt capacity names inum record value) := by
  unfold izrcpt; infer_instance
instance izrcpt_persistent inum record value : Persistent (izrcpt capacity names inum record value) := by
  unfold izrcpt; infer_instance
instance ireg_ep_timeless inum record : Timeless (ireg_ep capacity names inum record) := by
  unfold ireg_ep; infer_instance
instance nlz_obs_timeless inum epoch : Timeless (nlz_obs capacity names inum epoch) := by
  unfold nlz_obs; infer_instance
instance nlz_obs_persistent inum epoch : Persistent (nlz_obs capacity names inum epoch) := by
  unfold nlz_obs; infer_instance

theorem ireg_ep_intro inum record :
    iprop(⊢ LogEpoch.epochAuth capacity (names.observation inum) 0 ==∗
      ireg_ep capacity names inum record) := by
  iintro Ha
  imod LogEpoch.log_epoch_lb_0 capacity names.logEpoch with Hlb
  imodintro
  unfold ireg_ep
  iexists 0
  iframe Ha Hlb
  unfold izrcpt
  iintro _
  ileft
  ipureintro
  rfl

theorem ireg_ep_mono inum (old new : Dinode)
    (zero : new.nlink.toNat = 0 → old.nlink.toNat = 0) :
    iprop(ireg_ep capacity names inum old ⊢ ireg_ep capacity names inum new) := by
  unfold ireg_ep
  iintro ⟨%value, Ha, Hlb, Hreceipt⟩
  iexists value
  iframe Ha Hlb
  unfold izrcpt
  iintro %hz
  iapply Hreceipt
  ipureintro
  exact zero hz

theorem ireg_ep_mint inum record epoch (nonzero : record.nlink.toNat ≠ 0) :
    iprop(⊢ ireg_ep capacity names inum record -∗
      LogEpoch.log_epoch_lb capacity names.logEpoch epoch ==∗
      ireg_ep capacity names inum record ∗ nlz_obs capacity names inum epoch) := by
  unfold ireg_ep
  iintro ⟨%value, Ha, #Hlb, _⟩ #Hepoch
  imod LogEpoch.epoch_update capacity (names.observation inum) value (max value epoch)
    (Nat.le_max_left _ _) $$ Ha with ⟨Ha, #Hobs⟩
  have combine : iprop(⊢ LogEpoch.log_epoch_lb capacity names.logEpoch value -∗
      LogEpoch.log_epoch_lb capacity names.logEpoch epoch -∗
      LogEpoch.log_epoch_lb capacity names.logEpoch (max value epoch)) := by
    by_cases h : value ≤ epoch
    · rw [Nat.max_eq_right h]; iintro _ H; iexact H
    · rw [Nat.max_eq_left (by omega : epoch ≤ value)]; iintro H _; iexact H
  ihave #Hmax := combine $$ Hlb Hepoch
  imodintro
  isplitl [Ha]
  · iexists max value epoch
    iframe Ha Hmax
    unfold izrcpt
    iintro %hz
    exact (nonzero hz).elim
  · unfold nlz_obs
    iapply LogEpoch.log_epoch_lb_mono capacity (names.observation inum) (max value epoch)
      epoch (Nat.le_max_right _ _) $$ Hobs

theorem ireg_ep_use inum record epoch (zero : record.nlink.toNat = 0) (positive : 1 ≤ epoch) :
    iprop(⊢ ireg_ep capacity names inum record -∗ nlz_obs capacity names inum epoch -∗
      ireg_ep capacity names inum record ∗ ∃ logged : Nat, ⌜epoch ≤ logged⌝ ∗
        LogEpoch.logged_at capacity names.logged logged (iblkOf names inum)) := by
  iintro Hep Hobs
  iunfold ireg_ep at Hep
  icases Hep with ⟨%value, Ha, #Hlb, #Hreceipt⟩
  iunfold nlz_obs at Hobs
  ihave %bound := LogEpoch.log_epoch_lb_le capacity (names.observation inum) value epoch $$ Ha Hobs
  iunfold izrcpt at Hreceipt
  ihave Hresult := Hreceipt $$ []
  · ipureintro; exact zero
  · icases Hresult with (%never | ⟨%logged, #Hlogged, %upper⟩)
    · omega
    · isplitl [Ha]
      · unfold ireg_ep
        iexists value
        iframe Ha Hlb
        unfold izrcpt
        iexact Hreceipt
      · iexists logged
        iframe Hlogged
        ipureintro
        omega

theorem ireg_ep_open inum record :
    iprop(⊢ ireg_ep capacity names inum record -∗ ∃ value : Nat,
      LogEpoch.log_epoch_lb capacity names.logEpoch value ∗
      ∀ record' : Dinode, izrcpt capacity names inum record' value -∗
        ireg_ep capacity names inum record') := by
  unfold ireg_ep
  iintro ⟨%value, Ha, #Hlb, _⟩
  iexists value
  iframe Hlb
  iintro %record' Hreceipt
  iexists value
  iframe Ha Hlb Hreceipt

theorem actual : Spec capacity := ⟨ireg_ep_intro capacity, ireg_ep_mint capacity,
  ireg_ep_use capacity, ireg_ep_open capacity⟩

end MachCSL.Logic.IcacheEpoch
