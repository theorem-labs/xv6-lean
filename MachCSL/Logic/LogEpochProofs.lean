import MachCSL.Logic.LogEpochSpec

namespace MachCSL.Logic.LogEpoch
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI Auth
open Iris.Std.LawfulSet
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance epochAuth_timeless name e : Timeless (epochAuth capacity name e) := by
  unfold epochAuth; letI := capacity.monoNat name; infer_instance
instance log_epoch_lb_persistent name e : Persistent (log_epoch_lb capacity name e) := by
  unfold log_epoch_lb; letI := capacity.monoNat name; infer_instance
instance log_epoch_lb_timeless name e : Timeless (log_epoch_lb capacity name e) := by
  unfold log_epoch_lb; letI := capacity.monoNat name; infer_instance
instance loggedAuth_timeless name entries : Timeless (loggedAuth capacity name entries) := by
  unfold loggedAuth; infer_instance
instance logged_at_persistent name e b : Persistent (logged_at capacity name e b) := by
  unfold logged_at; infer_instance
instance logged_at_timeless name e b : Timeless (logged_at capacity name e b) := by
  unfold logged_at; infer_instance

theorem log_epoch_lb_get name epoch : iprop(⊢ epochAuth capacity name epoch -∗
    epochAuth capacity name epoch ∗ log_epoch_lb capacity name epoch) := by
  unfold epochAuth log_epoch_lb
  letI := capacity.monoNat name
  iintro Ha
  ihave #Hlb := MonoNat.lb_own_get name (.own 1) (.ofNat epoch) $$ Ha
  iframe Ha Hlb

theorem log_epoch_lb_le name epoch bound : iprop(⊢ epochAuth capacity name epoch -∗
    log_epoch_lb capacity name bound -∗ ⌜bound ≤ epoch⌝) := by
  unfold epochAuth log_epoch_lb
  letI := capacity.monoNat name
  iintro Ha Hl
  ihave %valid := MonoNat.auth_lb_own_valid name (.own 1) (.ofNat epoch) (.ofNat bound) $$ Ha Hl
  ipureintro
  exact valid.2

theorem log_epoch_lb_0 name : iprop(⊢ |==> log_epoch_lb capacity name 0) := by
  unfold log_epoch_lb
  letI := capacity.monoNat name
  exact MonoNat.lb_own_0 name

theorem log_epoch_lb_mono name epoch lower (bound : lower ≤ epoch) :
    iprop(log_epoch_lb capacity name epoch ⊢ log_epoch_lb capacity name lower) := by
  unfold log_epoch_lb
  letI := capacity.monoNat name
  iintro H
  iapply MonoNat.lb_own_le name (.ofNat epoch) (.ofNat lower) bound $$ H

theorem logged_at_in name entries epoch block :
    iprop(⊢ loggedAuth capacity name entries -∗ logged_at capacity name epoch block -∗
      ⌜(epoch, block) ∈ entries⌝) := by
  unfold loggedAuth logged_at
  iintro Ha Hf
  icases (iOwn_cmraValid_op (E := capacity.logged)) $$ [$Ha $Hf] with %valid
  ipureintro
  have included := (Auth.both_dfrac_valid_discrete.mp valid).2.1
  exact (LeibnizSet.included_iff_subset _ _).mp included (epoch, block) (mem_singleton.mpr rfl)

theorem logged_at_get name entries epoch block (member : (epoch, block) ∈ entries) :
    iprop(⊢ loggedAuth capacity name entries ==∗
      loggedAuth capacity name entries ∗ logged_at capacity name epoch block) := by
  unfold loggedAuth logged_at
  iintro Ha
  rw [← (iOwn_op (E := capacity.logged)).to_eq]
  iapply (iOwn_update (E := capacity.logged)) $$ Ha
  apply Auth.auth_update_dfrac_alloc
  apply (LeibnizSet.included_iff_subset _ _).mpr
  intro key hk
  obtain rfl := mem_singleton.mp hk
  exact member

theorem log_mint_logged name entries epoch block :
    iprop(⊢ loggedAuth capacity name entries ==∗
      loggedAuth capacity name (entries ∪ {(epoch, block)}) ∗ logged_at capacity name epoch block) := by
  iintro Ha
  ihave >Ha : |==> loggedAuth capacity name (entries ∪ {(epoch, block)}) $$ [Ha]
  · unfold loggedAuth
    iapply (iOwn_update (E := capacity.logged)) $$ Ha
    exact Auth.auth_update_auth (LeibnizSet.localUpdate entries ∅
      (entries ∪ {(epoch, block)}) union_subset_left)
  · iapply logged_at_get capacity name (entries ∪ {(epoch, block)}) epoch block
      (mem_union.mpr (.inr (mem_singleton.mpr rfl))) $$ Ha

theorem epoch_update name old next (bound : old ≤ next) :
    iprop(⊢ epochAuth capacity name old ==∗ epochAuth capacity name next ∗ log_epoch_lb capacity name next) := by
  unfold epochAuth log_epoch_lb
  letI := capacity.monoNat name
  exact MonoNat.own_update name (.ofNat old) (.ofNat next) bound

/-- Isolated fresh initialization of only the epoch and append-registry pair.
The source's lock/operation/transaction names are additional log_free_tok parts. -/
theorem allocate_genesis (frame : IProp GF) :
    iprop(frame ⊢ |==> ∃ epochName loggedName,
      epochAuth capacity epochName 1 ∗ loggedAuth capacity loggedName ∅ ∗ frame) := by
  letI := capacity.monoNat 0
  iintro Hframe
  imod MonoNat.own_alloc (GF := GF) (.ofNat 1) with ⟨%epochName, Ha, _⟩
  have alloc : iprop(⊢ |==> ∃ name, loggedAuth capacity name ∅) := by
    unfold loggedAuth
    apply iOwn_alloc (E := capacity.logged)
    exact Auth.auth_valid.mpr trivial
  imod alloc with ⟨%loggedName, Hl⟩
  imodintro
  iexists epochName, loggedName
  unfold epochAuth Capacity.monoNat MonoNat.auth_own
  iframe Ha Hl Hframe

theorem actual : Spec capacity := ⟨log_epoch_lb_get capacity, log_epoch_lb_le capacity,
  log_epoch_lb_0 capacity, log_mint_logged capacity, logged_at_in capacity⟩

end MachCSL.Logic.LogEpoch
