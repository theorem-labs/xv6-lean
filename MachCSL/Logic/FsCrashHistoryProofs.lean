import MachCSL.Logic.FsCrashPureProofs
import MachCSL.Logic.LockProofs

namespace MachCSL.Logic.FsCrash
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance historyAuth_timeless name history : Timeless (historyAuth capacity name history) := by
  unfold historyAuth; infer_instance
instance historyLowerBound_persistent name history : Persistent (historyLowerBound capacity name history) := by
  unfold historyLowerBound; infer_instance
instance historyLowerBound_timeless name history : Timeless (historyLowerBound capacity name history) := by
  unfold historyLowerBound; infer_instance
instance receipt_persistent names disk : Persistent (receipt capacity names disk) := by
  unfold receipt; infer_instance
instance receipt_timeless names disk : Timeless (receipt capacity names disk) := by
  unfold receipt; infer_instance
instance bootToken_timeless name : Timeless (bootToken capacity name) := by
  unfold bootToken; infer_instance
instance mirrorHalf_timeless name mirror : Timeless (mirrorHalf capacity name mirror) := by
  unfold mirrorHalf; letI := capacity.mirror; infer_instance
instance registered_persistent names generation era : Persistent (registered capacity names generation era) := by
  unfold registered Era.registered; letI := capacity.registry.entries; infer_instance
instance registered_timeless names generation era : Timeless (registered capacity names generation era) := by
  unfold registered Era.registered; letI := capacity.registry.entries; infer_instance
instance counterAuth_timeless name value : Timeless (counterAuth capacity name value) := by
  unfold counterAuth; infer_instance
instance counterLowerBound_persistent name value : Persistent (counterLowerBound capacity name value) := by
  unfold counterLowerBound; infer_instance
instance counterLowerBound_timeless name value : Timeless (counterLowerBound capacity name value) := by
  unfold counterLowerBound; infer_instance
instance started_persistent names generation : Persistent (started capacity names generation) := by
  unfold started; infer_instance
instance started_timeless names generation : Timeless (started capacity names generation) := by
  unfold started; infer_instance

theorem history_allocate history (frame : IProp GF) :
    iprop(frame ⊢ |==> ∃ name : GName, historyAuth capacity name history ∗ historyLowerBound capacity name history ∗ frame) := by
  iintro Hframe
  have valid := (MonoList.both_valid (historyEmbed history) (historyEmbed history)).mpr (by exact ⟨[], by simp⟩)
  imod iOwn_alloc (E := capacity.history) _ valid with ⟨%name, H⟩
  imodintro
  iexists name
  unfold historyAuth historyLowerBound
  ihave ⟨Ha, Hlb⟩ := (iOwn_op (E := capacity.history)).mp $$ H
  iframe

theorem history_snapshot name history : historyAuth capacity name history ⊢
    historyAuth capacity name history ∗ historyLowerBound capacity name history := by
  unfold historyAuth historyLowerBound
  rw [← (iOwn_op (E := capacity.history)).to_eq, ← MonoList.auth_lb_op]

theorem history_valid name history pre :
    historyAuth capacity name history ∗ historyLowerBound capacity name pre ⊢ ⌜pre <+: history⌝ := by
  unfold historyAuth historyLowerBound
  iintro H
  ihave %valid := (iOwn_cmraValid_op (E := capacity.history)) $$ H
  ipureintro
  exact (historyEmbed_prefix pre history).mp ((MonoList.both_valid _ _).mp valid)

theorem history_update name history next (prefixOf : history <+: next) :
    iprop(⊢ historyAuth capacity name history ==∗ historyAuth capacity name next) := by
  unfold historyAuth
  iintro H
  iapply (iOwn_update (E := capacity.history)) $$ H
  exact MonoList.update _ ((historyEmbed_prefix _ _).mpr prefixOf)

theorem boot_allocate (frame : IProp GF) : iprop(frame ⊢ |==> ∃ name : GName, bootToken capacity name ∗ frame) := by
  iintro Hframe
  imod Lock.allocate_free capacity.lock with ⟨%name, _, Hfrag⟩
  imodintro
  iexists name
  iframe Hframe
  unfold bootToken Lock.frag
  iexists 0
  iexact Hfrag

theorem boot_exclusive name : bootToken capacity name ∗ bootToken capacity name ⊢ False := by
  unfold bootToken
  iintro ⟨Hl, Hr⟩
  iapply Lock.frag_exclusive capacity.lock name none none $$ Hl Hr

theorem counter_valid name value lower :
    counterAuth capacity name value ∗ counterLowerBound capacity name lower ⊢ ⌜lower ≤ value⌝ := by
  unfold counterAuth counterLowerBound
  letI : MonoNatG GF := ⟨capacity.mono, name⟩
  iintro ⟨Ha, Hl⟩
  ihave %valid := MonoNat.auth_lb_own_valid name (.own 1) (.ofNat value) (.ofNat lower) $$ Ha Hl
  ipureintro; exact valid.2

theorem counter_update name old next (bound : old ≤ next) :
    iprop(⊢ counterAuth capacity name old ==∗ counterAuth capacity name next ∗ counterLowerBound capacity name next) := by
  unfold counterAuth counterLowerBound
  letI : MonoNatG GF := ⟨capacity.mono, name⟩
  exact MonoNat.own_update name (.ofNat old) (.ofNat next) bound

theorem historySpec : HistorySpec capacity :=
  ⟨history_allocate capacity, history_snapshot capacity, history_valid capacity,
    history_update capacity, boot_allocate capacity, boot_exclusive capacity⟩

end MachCSL.Logic.FsCrash
