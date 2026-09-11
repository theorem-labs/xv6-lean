import MachCSL.Logic.IcacheTypeGhostSpec

namespace MachCSL.Logic.IcacheTypeGhost
open Iris Iris.BI Iris.CMRA

theorem pending_valid : ✓ pendingElem := trivial
theorem shot_valid (ty : BitVec 16) : ✓ shotElem ty := Agree.toAgree_valid
instance pending_exclusive : Exclusive pendingElem := by unfold pendingElem; infer_instance
instance shot_coreId (ty : BitVec 16) : CoreId (shotElem ty) := by unfold shotElem; infer_instance

theorem pending_update (ty : BitVec 16) : pendingElem ~~> shotElem ty := Update.exclusive (shot_valid ty)
theorem shot_agree (ty ty' : BitVec 16) (h : ✓ (shotElem ty • shotElem ty')) : ty = ty' := by
  have eq : (⟨ty⟩ : DiscreteO (BitVec 16)) = ⟨ty'⟩ := toAgree_op_valid_iff_eq.mp h
  exact congrArg DiscreteO.car eq
theorem pending_pending_invalid : ¬ ✓ (pendingElem • pendingElem) := id
theorem pending_shot_invalid (ty : BitVec 16) : ¬ ✓ (pendingElem • shotElem ty) := id

variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance ity_pending_timeless g : Timeless (ity_pending capacity g) := by unfold ity_pending; infer_instance
instance ity_shot_timeless g ty : Timeless (ity_shot capacity g ty) := by unfold ity_shot; infer_instance
instance ity_shot_persistent g ty : Persistent (ity_shot capacity g ty) := by unfold ity_shot; infer_instance
instance ireg_boot_timeless g : Timeless (ireg_boot capacity g) := by unfold ireg_boot; infer_instance
instance ireg_open_timeless g : Timeless (ireg_open capacity g) := by unfold ireg_open; infer_instance
instance ireg_open_persistent g : Persistent (ireg_open capacity g) := by unfold ireg_open; infer_instance
instance ireg_regime_timeless g rg : Timeless (ireg_regime capacity g rg) := by
  unfold ireg_regime; split <;> infer_instance
instance ireg_regime_true_persistent g : Persistent (ireg_regime capacity g true) := by
  change Persistent (ireg_open capacity g); infer_instance

theorem ity_shoot g ty : iprop(ity_pending capacity g ⊢ |==> ity_shot capacity g ty) :=
  iOwn_update (E := capacity.type) (pending_update ty)

theorem ity_shot_agree g ty ty' : iprop(ity_shot capacity g ty ∗ ity_shot capacity g ty' ⊢ ⌜ty = ty'⌝) := by
  unfold ity_shot
  iintro ⟨H,H'⟩
  ihave %valid := iOwn_cmraValid_op (E := capacity.type) $$ [$H $H']
  ipureintro; exact shot_agree ty ty' valid

theorem ity_pending_excl g : iprop(ity_pending capacity g ∗ ity_pending capacity g ⊢ False) := by
  unfold ity_pending
  iintro ⟨H,H'⟩
  ihave %valid := iOwn_cmraValid_op (E := capacity.type) $$ [$H $H']
  exact (pending_pending_invalid valid).elim

theorem ity_pending_shot_excl g ty : iprop(ity_pending capacity g ∗ ity_shot capacity g ty ⊢ False) := by
  unfold ity_pending ity_shot
  iintro ⟨H,H'⟩
  ihave %valid := iOwn_cmraValid_op (E := capacity.type) $$ [$H $H']
  exact (pending_shot_invalid ty valid).elim

theorem ireg_boot_open_excl g : iprop(ireg_boot capacity g ∗ ireg_open capacity g ⊢ False) := by
  unfold ireg_boot ireg_open
  iintro ⟨Hb,⟨%ty,Hs⟩⟩
  iapply ity_pending_shot_excl capacity g ty $$ [$Hb $Hs]

theorem ireg_regime_true g : ireg_regime capacity g true = ireg_open capacity g := rfl
theorem ireg_regime_false g : ireg_regime capacity g false = ireg_boot capacity g := rfl

theorem ireg_regime_boot_excl g rg : iprop(ireg_regime capacity g rg ∗ ireg_boot capacity g ⊢ False) := by
  cases rg
  · exact ity_pending_excl capacity g
  · change iprop(ireg_open capacity g ∗ ireg_boot capacity g ⊢ False)
    iintro ⟨Ho,Hb⟩
    iapply ireg_boot_open_excl capacity g $$ [$Hb $Ho]

/-- Exact zero witness chosen by `FsReady.fs_ready_seal`. -/
theorem fs_ready_seal g : iprop(ireg_boot capacity g ⊢ |==> ireg_open capacity g) := by
  unfold ireg_boot ireg_open
  iintro H
  imod ity_shoot capacity g (0#16) $$ H with H
  imodintro; iexists 0#16; iexact H

theorem allocate_pending (frame : IProp GF) : iprop(frame ⊢ |==> ∃ g, ity_pending capacity g ∗ frame) := by
  iintro HR
  imod iOwn_alloc (E := capacity.type) pendingElem pending_valid with ⟨%g,H⟩
  imodintro; iexists g
  unfold ity_pending
  iframe H HR

theorem shoot_frame g ty (frame : IProp GF) :
    iprop(ity_pending capacity g ∗ frame ⊢ |==> (ity_shot capacity g ty ∗ frame)) := by
  iintro ⟨H,HR⟩
  imod ity_shoot capacity g ty $$ H with H
  imodintro; iframe H HR

/-- Only the already-extracted slot guard is used here. This is not the
source invariant-opening accessor `IregLinkNz.ireg_boot_no_claim`. -/
theorem claim_guard {α : Type} (g : GName) (c : Option α) :
    iprop((⌜c = none⌝ ∨ ireg_open capacity g) ∗ ireg_boot capacity g ⊢
      ⌜c = none⌝ ∗ ireg_boot capacity g) := by
  iintro ⟨H,Hb⟩
  icases H with (H | H)
  · iframe H Hb
  · ihave Hfalse := ireg_boot_open_excl capacity g $$ [$Hb $H]
    icases Hfalse with ⟨⟩

/-- These examples keep zero and nonzero firing in the public checked API. -/
theorem shoot_zero g : iprop(ity_pending capacity g ⊢ |==> ity_shot capacity g 0#16) := ity_shoot capacity g _
theorem shoot_nonzero g : iprop(ity_pending capacity g ⊢ |==> ity_shot capacity g 2#16) := ity_shoot capacity g _

theorem actual : Spec capacity where
  shoot := ity_shoot capacity
  agree := ity_shot_agree capacity
  pendingExclusive := ity_pending_excl capacity
  pendingShotExclusive := ity_pending_shot_excl capacity
  sealBoot := fs_ready_seal capacity
  regimeBootExclusive := ireg_regime_boot_excl capacity
  allocate := allocate_pending capacity

end MachCSL.Logic.IcacheTypeGhost
