import MachCSL.Logic.LockSetSpec
import MachCSL.Logic.LockRankProofs

namespace MachCSL.Logic.LockSet
open Iris Iris.Std Iris.Std.LawfulSet Iris.Algebra Iris.CMRA Iris.BI Auth

theorem both_member (held : Names) (name : String)
    (valid : ✓ (authElem held • fragElem name)) : name ∈ held := by
  have included := (Auth.both_dfrac_valid_discrete.mp valid).2.1
  exact DisjointLeibnizSet.included_iff_subset.mp included name (mem_singleton.mpr rfl)

theorem fragments_invalid (name : String) : ¬ ✓ (fragElem name • fragElem name) := by
  intro valid
  have disjoint := DisjointLeibnizSet.valid_op_iff_disj.mp (Auth.frag_op_valid.mp valid)
  exact disjoint name ⟨mem_singleton.mpr rfl, mem_singleton.mpr rfl⟩

theorem insert_update (held : Names) (name : String) (absent : name ∉ held) :
    authElem held ~~> authElem ({name} ∪ held) • fragElem name := by
  apply Auth.auth_update_alloc
  apply DisjointLeibnizSet.localUpdate_alloc_empty_of_disj
  intro other pair
  exact absent ((mem_singleton.mp pair.1) ▸ pair.2)

theorem delete_update (held : Names) (name : String) :
    authElem held • fragElem name ~~> authElem (held \ {name}) :=
  Auth.auth_update_dealloc DisjointLeibnizSet.localUpdate_dealloc

variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance auth_timeless γ held : Timeless (auth capacity γ held) := by
  unfold auth
  infer_instance
instance member_timeless γ name : Timeless (member capacity γ name) := by
  unfold member
  infer_instance
instance level_timeless γ depth held : Timeless (level capacity γ depth held) := by
  unfold level
  infer_instance

theorem agree γ held name :
    iprop(⊢ auth capacity γ held -∗ member capacity γ name -∗ ⌜name ∈ held⌝) := by
  unfold auth member
  iintro Ha Hf
  ihave %valid := iOwn_cmraValid_op (E := capacity.set) $$ [$Ha $Hf]
  ipureintro
  exact both_member held name valid

theorem not_member γ held name (absent : name ∉ held) :
    iprop(⊢ auth capacity γ held -∗ member capacity γ name -∗ False) := by
  iintro Ha Hf
  ihave %present := agree capacity γ held name $$ Ha Hf
  ipureintro
  exact absent present

theorem not_member_below γ held name (below : LockRank.Below held name) :
    iprop(⊢ auth capacity γ held -∗ member capacity γ name -∗ False) :=
  not_member capacity γ held name (LockRank.below_not_mem below)

theorem exclusive γ name :
    iprop(⊢ member capacity γ name -∗ member capacity γ name -∗ False) := by
  unfold member
  iintro Hl Hr
  ihave %valid := iOwn_cmraValid_op (E := capacity.set) $$ [$Hl $Hr]
  ipureintro
  exact fragments_invalid name valid

theorem insert γ held name (absent : name ∉ held) :
    iprop(⊢ auth capacity γ held ==∗
      auth capacity γ ({name} ∪ held) ∗ member capacity γ name) := by
  unfold auth member
  rw [← (iOwn_op (E := capacity.set)).to_eq]
  iintro H
  iapply iOwn_update (E := capacity.set) (insert_update held name absent) $$ H

theorem insert_below γ held name (below : LockRank.Below held name) :
    iprop(⊢ auth capacity γ held ==∗
      auth capacity γ ({name} ∪ held) ∗ member capacity γ name) :=
  insert capacity γ held name (LockRank.below_not_mem below)

theorem delete γ held name :
    iprop(⊢ auth capacity γ held -∗ member capacity γ name ==∗
      ⌜name ∈ held⌝ ∗ auth capacity γ (held \ {name})) := by
  iintro Ha Hf
  ihave %present := agree capacity γ held name $$ Ha Hf
  unfold auth member
  ihave H := (iOwn_op (E := capacity.set)).mpr $$ [$Ha $Hf]
  imod iOwn_update (E := capacity.set) (delete_update held name) $$ H with Ha
  imodintro
  isplitr
  · ipureintro
    exact present
  · iexact Ha

theorem allocate : iprop(⊢ |==> ∃ γ, auth capacity γ ∅) := by
  unfold auth
  apply iOwn_alloc (E := capacity.set)
  exact Auth.auth_valid.mpr trivial

theorem level_unfold γ depth held :
    iprop(level capacity γ depth held ⊣⊢ auth capacity γ held ∗ ⌜held.size ≤ depth⌝) := .rfl

theorem level_intro γ depth held (bound : held.size ≤ depth) :
    iprop(⊢ auth capacity γ held -∗ level capacity γ depth held) := by
  unfold level
  iintro H
  iframe H
  ipureintro
  exact bound

theorem level_relevel γ depth depth' held (bound : held.size ≤ depth') :
    iprop(⊢ level capacity γ depth held -∗ level capacity γ depth' held) := by
  unfold level
  iintro ⟨H, _⟩
  iframe H
  ipureintro
  exact bound

theorem level_weaken γ depth depth' held (le : depth ≤ depth') :
    iprop(⊢ level capacity γ depth held -∗ level capacity γ depth' held) := by
  unfold level
  iintro ⟨H, %bound⟩
  iframe H
  ipureintro
  exact Nat.le_trans bound le

theorem level_zero γ held :
    iprop(⊢ level capacity γ 0 held -∗ auth capacity γ held ∗ ⌜held = ∅⌝) := by
  unfold level
  iintro ⟨H, %bound⟩
  iframe H
  ipureintro
  exact LockRank.size_le_zero_empty held bound

/-- Acquire's actual set/depth coupling step, with freshness retained. -/
theorem level_insert γ depth held name (absent : name ∉ held) :
    iprop(⊢ level capacity γ depth held ==∗
      level capacity γ (depth + 1) ({name} ∪ held) ∗ member capacity γ name) := by
  unfold level
  iintro ⟨H, %bound⟩
  imod insert capacity γ held name absent $$ H with ⟨H, Hf⟩
  imodintro
  iframe Hf H
  ipureintro
  exact LockRank.size_add_le name held depth absent bound

/-- Deleting the owned family pays precisely pop_off's smaller bound. -/
theorem level_delete γ depth held name :
    iprop(⊢ level capacity γ (depth + 1) held -∗ member capacity γ name ==∗
      ⌜name ∈ held⌝ ∗ level capacity γ depth (held \ {name})) := by
  unfold level
  iintro ⟨H, %bound⟩ Hf
  imod delete capacity γ held name $$ H Hf with ⟨%present, H⟩
  imodintro
  isplitr
  · ipureintro
    exact present
  · iframe H
    ipureintro
    exact LockRank.size_delete_lt name held depth present bound

theorem cpu_agree era cpu held name :
    iprop(⊢ cpuLocks capacity era cpu held -∗ cpuMember capacity era cpu name -∗ ⌜name ∈ held⌝) :=
  agree capacity (era.heldLocks cpu) held name

theorem cpu_insert era cpu held name (absent : name ∉ held) :
    iprop(⊢ cpuLocks capacity era cpu held ==∗
      cpuLocks capacity era cpu ({name} ∪ held) ∗ cpuMember capacity era cpu name) :=
  insert capacity (era.heldLocks cpu) held name absent

theorem cpu_delete era cpu held name :
    iprop(⊢ cpuLocks capacity era cpu held -∗ cpuMember capacity era cpu name ==∗
      ⌜name ∈ held⌝ ∗ cpuLocks capacity era cpu (held \ {name})) :=
  delete capacity (era.heldLocks cpu) held name

theorem actual : LockSetSpec capacity where
  agree := agree capacity
  exclusive := exclusive capacity
  insert := insert capacity
  delete := delete capacity
  allocate := allocate capacity
  levelIntro := level_intro capacity
  relevel := level_relevel capacity
  levelZero := level_zero capacity
  levelInsert := level_insert capacity
  levelDelete := level_delete capacity

end MachCSL.Logic.LockSet
