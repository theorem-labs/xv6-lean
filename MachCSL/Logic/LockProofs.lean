import MachCSL.Logic.LockSpec

namespace MachCSL.Logic.Lock
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

theorem both_valid state position : ✓ (authElem state position • fragElem state position) :=
  ⟨ExclAuth.valid, ExclAuth.valid⟩

theorem both_agree state state' position position'
    (valid : ✓ (authElem state position • fragElem state' position')) :
    state = state' ∧ position = position' :=
  ⟨congrArg (·.car) (ExclAuth.agree valid.1), congrArg (·.car) (ExclAuth.agree valid.2)⟩

theorem fragments_invalid state state' position position' :
    ¬ ✓ (fragElem state position • fragElem state' position') :=
  fun valid => ExclAuth.frag_op_valid.mp valid.1

theorem authorities_invalid state state' position position' :
    ¬ ✓ (authElem state position • authElem state' position') :=
  fun valid => ExclAuth.auth_op_valid.mp valid.1

theorem both_update state state' position position' :
    (authElem state position • fragElem state position) ~~>
      (authElem state' position' • fragElem state' position') :=
  Update.prod _ ExclAuth.update ExclAuth.update

variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance authAt_timeless γ state position : Timeless (authAt capacity γ state position) := by
  unfold authAt
  infer_instance
instance fragAt_timeless γ state position : Timeless (fragAt capacity γ state position) := by
  unfold fragAt
  infer_instance
instance auth_timeless γ state : Timeless (auth capacity γ state) := by unfold auth; infer_instance
instance frag_timeless γ state : Timeless (frag capacity γ state) := by unfold frag; infer_instance

/-- Split ownership of the combined native element into its two exclusive
roles. These are authority/fragment roles, not fractional DFrac shares. -/
theorem both_split γ state position :
    iOwn (E := capacity.lock) γ (authElem state position • fragElem state position) ⊣⊢
      authAt capacity γ state position ∗ fragAt capacity γ state position := iOwn_op (E := capacity.lock)

theorem position_agree γ state state' position position' :
    iprop(⊢ authAt capacity γ state position -∗ fragAt capacity γ state' position' -∗
      ⌜state = state' ∧ position = position'⌝) := by
  unfold authAt fragAt
  iintro Ha Hf
  ihave %valid := iOwn_cmraValid_op (E := capacity.lock) $$ [$Ha $Hf]
  ipureintro
  exact both_agree state state' position position' valid

theorem state_agree γ state state' :
    iprop(⊢ auth capacity γ state -∗ frag capacity γ state' -∗ ⌜state = state'⌝) := by
  unfold auth frag
  iintro ⟨%position, Ha⟩ ⟨%position', Hf⟩
  ihave %same := position_agree capacity γ state state' position position' $$ Ha Hf
  ipureintro
  exact same.1

theorem fragAt_exclusive γ state state' position position' :
    iprop(⊢ fragAt capacity γ state position -∗ fragAt capacity γ state' position' -∗ False) := by
  unfold fragAt
  iintro Hl Hr
  ihave %valid := iOwn_cmraValid_op (E := capacity.lock) $$ [$Hl $Hr]
  ipureintro
  exact fragments_invalid state state' position position' valid

theorem frag_exclusive γ state state' :
    iprop(⊢ frag capacity γ state -∗ frag capacity γ state' -∗ False) := by
  unfold frag
  iintro ⟨%position, Hl⟩ ⟨%position', Hr⟩
  iapply fragAt_exclusive capacity γ state state' position position' $$ Hl Hr

theorem authAt_exclusive γ state state' position position' :
    iprop(⊢ authAt capacity γ state position -∗ authAt capacity γ state' position' -∗ False) := by
  unfold authAt
  iintro Hl Hr
  ihave %valid := iOwn_cmraValid_op (E := capacity.lock) $$ [$Hl $Hr]
  ipureintro
  exact authorities_invalid state state' position position' valid

theorem updateAt γ state state' position position' :
    iprop(⊢ authAt capacity γ state position -∗ fragAt capacity γ state position ==∗
      authAt capacity γ state' position' ∗ fragAt capacity γ state' position') := by
  iintro Ha Hf
  ihave H := (both_split capacity γ state position).mpr $$ [$Ha $Hf]
  imod iOwn_update (E := capacity.lock) (both_update state state' position position') $$ H with H
  imodintro
  iapply (both_split capacity γ state' position').mp $$ H

theorem updateAt_frame γ state state' position position' (frame : IProp GF) :
    iprop(⊢ authAt capacity γ state position -∗ (fragAt capacity γ state position ∗ frame) ==∗
      authAt capacity γ state' position' ∗ fragAt capacity γ state' position' ∗ frame) := by
  iintro Ha ⟨Hf, HR⟩
  imod updateAt capacity γ state state' position position' $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe Ha Hf HR

theorem update_state γ state state' :
    iprop(⊢ auth capacity γ state -∗ frag capacity γ state ==∗ auth capacity γ state' ∗ frag capacity γ state') := by
  unfold auth frag
  iintro ⟨%position, Ha⟩ ⟨%position', Hf⟩
  ihave %same := position_agree capacity γ state state position position' $$ Ha Hf
  rcases same.2 with rfl
  imod updateAt capacity γ state state' position position $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  isplitl [Ha]
  · iexists position
    iexact Ha
  · iexists position
    iexact Hf

/-- Acquisition chooses the actual AMO position; no instruction, floor, or
holder protocol is asserted by this camera update alone. -/
theorem acquire_at γ (cpu : MachCSL.Machine.CPU) oldPosition position :
    iprop(⊢ authAt capacity γ none oldPosition -∗ fragAt capacity γ none oldPosition ==∗
      authAt capacity γ (some (cpu, false)) position ∗ fragAt capacity γ (some (cpu, false)) position) :=
  updateAt capacity γ none (some (cpu, false)) oldPosition position

theorem set_cpu_at γ (cpu : MachCSL.Machine.CPU) position :
    iprop(⊢ authAt capacity γ (some (cpu, false)) position -∗
      fragAt capacity γ (some (cpu, false)) position ==∗
      authAt capacity γ (some (cpu, true)) position ∗ fragAt capacity γ (some (cpu, true)) position) :=
  updateAt capacity γ (some (cpu, false)) (some (cpu, true)) position position

theorem clear_cpu_at γ (cpu : MachCSL.Machine.CPU) position :
    iprop(⊢ authAt capacity γ (some (cpu, true)) position -∗
      fragAt capacity γ (some (cpu, true)) position ==∗
      authAt capacity γ (some (cpu, false)) position ∗ fragAt capacity γ (some (cpu, false)) position) :=
  updateAt capacity γ (some (cpu, true)) (some (cpu, false)) position position

theorem release_at γ (cpu : MachCSL.Machine.CPU) position :
    iprop(⊢ authAt capacity γ (some (cpu, false)) position -∗
      fragAt capacity γ (some (cpu, false)) position ==∗
      authAt capacity γ none position ∗ fragAt capacity γ none position) :=
  updateAt capacity γ (some (cpu, false)) none position position

theorem allocate state position : iprop(⊢ |==> ∃ γ,
    authAt capacity γ state position ∗ fragAt capacity γ state position) := by
  imod iOwn_alloc (E := capacity.lock) (authElem state position • fragElem state position)
    (both_valid state position) with ⟨%γ, H⟩
  imodintro
  iexists γ
  iapply (both_split capacity γ state position).mp $$ H

theorem allocate_free : iprop(⊢ |==> ∃ γ, authAt capacity γ none 0 ∗ fragAt capacity γ none 0) :=
  allocate capacity none 0

theorem actual : LockSpec capacity where
  agree := position_agree capacity
  exclusive := fragAt_exclusive capacity
  update := updateAt capacity
  allocate := allocate capacity

end MachCSL.Logic.Lock
