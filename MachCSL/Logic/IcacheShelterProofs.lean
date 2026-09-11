import MachCSL.Logic.IcacheShelterSpec
import MachCSL.Logic.IcacheTypeGhostProofs
import MachCSL.Logic.LogTxProofs
import MachCSL.Logic.IcacheSlotCouplingPureProofs

namespace MachCSL.Logic.IcacheShelter
open Iris Iris.BI IcacheRefLedger IcacheSlotCoupling

theorem cty_pin_none : cty_pin none = none := rfl
theorem cty_pin_invalid : cty_pin (some .invalid) = none := rfl
theorem cty_pin_claim ty t q : cty_pin (claimCell ty t q) = some (t,q) := rfl

variable {GF : BundledGFunctors} (types : IcacheTypeGhost.Capacity GF)
    (transactions : LogTx.Capacity GF)

instance ireg_fpin_timeless tx rg : Timeless (ireg_fpin transactions tx rg) := by
  unfold ireg_fpin; infer_instance
instance ireg_cpin_timeless tx c : Timeless (ireg_cpin transactions tx c) := by
  unfold ireg_cpin; infer_instance
instance ireg_fsh_timeless boot tx f : Timeless (ireg_fsh types transactions boot tx f) := by
  cases f with
  | none => unfold ireg_fsh; infer_instance
  | some x => cases x with
    | invalid => unfold ireg_fsh; infer_instance
    | excl phase => cases phase with | mk phase => cases phase <;> unfold ireg_fsh <;> infer_instance
instance ireg_shp_timeless boot tx c f : Timeless (ireg_shp types transactions boot tx c f) := by
  unfold ireg_shp; infer_instance

theorem ireg_fsh_off boot tx : iprop(⊢ ireg_fsh types transactions boot tx (freezeCell .off)) := by
  exact BI.true_intro

theorem ireg_fsh_pre boot tx rg :
    iprop(⊢ IcacheTypeGhost.ireg_regime types boot rg.1 -∗ ireg_fpin transactions tx rg -∗
      ireg_fsh types transactions boot tx (freezeCell (.pre rg))) := by
  change iprop(⊢ IcacheTypeGhost.ireg_regime types boot rg.1 -∗ ireg_fpin transactions tx rg -∗
    IcacheTypeGhost.ireg_regime types boot rg.1 ∗ ireg_fpin transactions tx rg)
  iintro Hr Hp
  iframe Hr Hp

theorem ireg_fsh_post_acc boot tx rg :
    iprop(ireg_fsh types transactions boot tx (freezeCell (.post rg)) ⊢
      IcacheTypeGhost.ireg_regime types boot rg.1 ∗ ireg_fpin transactions tx rg) := .rfl

/-- Both pre and post retain the exact supplied full index. -/
theorem ireg_fsh_pre_post boot tx rg :
    iprop(ireg_fsh types transactions boot tx (freezeCell (.pre rg)) ⊣⊢
      ireg_fsh types transactions boot tx (freezeCell (.post rg))) := .rfl

theorem ireg_fsh_none boot tx : ireg_fsh types transactions boot tx none =
    iprop(IcacheTypeGhost.ireg_open types boot ∨ IcacheTypeGhost.ireg_boot types boot) := rfl
theorem ireg_fsh_invalid boot tx : ireg_fsh types transactions boot tx (some .invalid) =
    iprop(IcacheTypeGhost.ireg_open types boot ∨ IcacheTypeGhost.ireg_boot types boot) := rfl

theorem ireg_fsh_no_ops boot tx f n d (valid : ireg_frz_ok f n d) :
    iprop(⊢ LogTx.auth transactions tx ∅ -∗ ireg_fsh types transactions boot tx f -∗ ⌜f = freezeCell .off⌝) := by
  cases f with
  | none => exact valid.elim
  | some x => cases x with
    | invalid => exact valid.elim
    | excl phase => cases phase with | mk phase => cases phase with
      | off => iintro _ _; ipureintro; rfl
      | pre rg =>
        change iprop(⊢ LogTx.auth transactions tx ∅ -∗
          (IcacheTypeGhost.ireg_regime types boot rg.1 ∗ LogTx.tx_pin transactions tx rg.2.1 rg.2.2) -∗ _)
        iintro Ha ⟨_,Hp⟩
        ihave %bad := LogTx.tx_pin_no_ops transactions tx rg.2.1 rg.2.2 $$ Ha Hp
        exact bad.elim
      | post rg =>
        change iprop(⊢ LogTx.auth transactions tx ∅ -∗
          (IcacheTypeGhost.ireg_regime types boot rg.1 ∗ LogTx.tx_pin transactions tx rg.2.1 rg.2.2) -∗ _)
        iintro Ha ⟨_,Hp⟩
        ihave %bad := LogTx.tx_pin_no_ops transactions tx rg.2.1 rg.2.2 $$ Ha Hp
        exact bad.elim

private theorem malformed_boot_excl boot :
    iprop(⊢ (IcacheTypeGhost.ireg_open types boot ∨ IcacheTypeGhost.ireg_boot types boot) -∗
      IcacheTypeGhost.ireg_boot types boot -∗ False) := by
  iintro H Hb
  icases H with (Ho | Hp)
  · iapply IcacheTypeGhost.ireg_boot_open_excl types boot $$ [$Hb $Ho]
  · have excl : iprop(IcacheTypeGhost.ireg_boot types boot ∗ IcacheTypeGhost.ireg_boot types boot ⊢ False) :=
      IcacheTypeGhost.ity_pending_excl types boot
    iapply excl $$ [$Hp $Hb]

theorem ireg_fsh_boot_off boot tx f :
    iprop(⊢ ireg_fsh types transactions boot tx f -∗ IcacheTypeGhost.ireg_boot types boot -∗
      ⌜f = freezeCell .off⌝) := by
  cases f with
  | none =>
    rw [ireg_fsh_none]
    iintro H Hb
    ihave %bad := malformed_boot_excl types boot $$ H Hb
    exact bad.elim
  | some x => cases x with
    | invalid =>
      rw [ireg_fsh_invalid]
      iintro H Hb
      ihave %bad := malformed_boot_excl types boot $$ H Hb
      exact bad.elim
    | excl phase => cases phase with | mk phase => cases phase with
      | off => iintro _ _; ipureintro; rfl
      | pre rg =>
        change iprop(⊢ (IcacheTypeGhost.ireg_regime types boot rg.1 ∗ ireg_fpin transactions tx rg) -∗
          IcacheTypeGhost.ireg_boot types boot -∗ _)
        iintro ⟨Hr,_⟩ Hb
        ihave %bad := IcacheTypeGhost.ireg_regime_boot_excl types boot rg.1 $$ [$Hr $Hb]
        exact bad.elim
      | post rg =>
        change iprop(⊢ (IcacheTypeGhost.ireg_regime types boot rg.1 ∗ ireg_fpin transactions tx rg) -∗
          IcacheTypeGhost.ireg_boot types boot -∗ _)
        iintro ⟨Hr,_⟩ Hb
        ihave %bad := IcacheTypeGhost.ireg_regime_boot_excl types boot rg.1 $$ [$Hr $Hb]
        exact bad.elim

theorem ireg_fsh_step boot tx ph ph' (allowed : ph' = .off ∨ frz_reg ph' = frz_reg ph) :
    iprop(ireg_fsh types transactions boot tx (freezeCell ph) ⊢
      ireg_fsh types transactions boot tx (freezeCell ph')) := by
  rcases allowed with rfl | same
  · iintro _; iapply ireg_fsh_off types transactions boot tx
  · cases ph' with
    | off => iintro _; iapply ireg_fsh_off types transactions boot tx
    | pre rg' =>
      cases ph with
      | off => cases same
      | pre rg => have eq : rg' = rg := Option.some.inj same; subst rg'; exact .rfl
      | post rg => have eq : rg' = rg := Option.some.inj same; subst rg'; exact .rfl
    | post rg' =>
      cases ph with
      | off => cases same
      | pre rg => have eq : rg' = rg := Option.some.inj same; subst rg'; exact .rfl
      | post rg => have eq : rg' = rg := Option.some.inj same; subst rg'; exact .rfl

theorem ireg_cpin_none tx : iprop(⊢ ireg_cpin transactions tx none) := by
  change iprop(⊢ emp)
  exact .rfl

theorem ireg_cpin_some tx (v : ClaimValue) :
    iprop(LogTx.tx_pin transactions tx v.2.1 v.2.2 ⊢ ireg_cpin transactions tx (some (.excl ⟨v⟩))) := .rfl

theorem ireg_cpin_some_elem tx (v : ClaimValue) :
    ireg_cpin transactions tx (some (.excl ⟨v⟩)) =
      (letI := transactions.transactions
       ghost_map_elem (H := LogTx.TxMap) tx (.own v.2.2) v.2.1 () : IProp GF) := rfl

theorem ireg_cpin_no_ops tx c f d (valid : ireg_claim_ok c f d) :
    iprop(⊢ LogTx.auth transactions tx ∅ -∗ ireg_cpin transactions tx c -∗ ⌜c = none⌝) := by
  iintro Ha Hp
  iunfold ireg_cpin at Hp
  ihave %empty := LogTx.tx_pin_o_no_ops transactions tx (cty_pin c) $$ Ha Hp
  ipureintro
  cases c with
  | none => rfl
  | some x => cases x with
    | invalid => exact valid.2.2.elim
    | excl claim => cases empty

theorem ireg_shp_intro boot tx c f :
    iprop(⊢ ireg_fsh types transactions boot tx f -∗ ireg_cpin transactions tx c -∗
      ireg_shp types transactions boot tx c f) := by
  unfold ireg_shp
  iintro Hf Hc; iframe Hf Hc

theorem ireg_shp_split boot tx c f :
    iprop(ireg_shp types transactions boot tx c f ⊢
      ireg_fsh types transactions boot tx f ∗ ireg_cpin transactions tx c) := .rfl

theorem ireg_shp_iff boot tx c f :
    iprop(ireg_shp types transactions boot tx c f ⊣⊢
      ireg_fsh types transactions boot tx f ∗ ireg_cpin transactions tx c) := .rfl

theorem ireg_shp_none boot tx f :
    iprop(ireg_fsh types transactions boot tx f ⊢ ireg_shp types transactions boot tx none f) := by
  unfold ireg_shp
  iintro Hf
  iframe Hf
  iapply ireg_cpin_none transactions tx

theorem actual : Spec types transactions where
  freezeNoOps := ireg_fsh_no_ops types transactions
  claimNoOps := ireg_cpin_no_ops transactions
  bootOff := ireg_fsh_boot_off types transactions
  phase := ireg_fsh_step types transactions
  split := ireg_shp_iff types transactions

end MachCSL.Logic.IcacheShelter
