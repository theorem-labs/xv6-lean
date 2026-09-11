import MachCSL.Logic.IcacheRefLedgerSpec

namespace MachCSL.Logic.IcacheRefLedger
open Iris Iris.Std Iris.CMRA Iris.BI
open scoped CommMonoidLike

theorem nat_add_op (r s : Nat) : (⟨r⟩ : NatAdd) • (⟨s⟩ : NatAdd) = (⟨r + s⟩ : NatAdd) := rfl
theorem nat_add_included (r s : Nat) : (⟨r⟩ : NatAdd) ≼ ⟨s⟩ ↔ r ≤ s := CommMonoidLike.inc_iff_le

theorem both_valid i a b (valid : ✓ (authElem i a • fragElem i b)) : b ≼ a ∧ ✓ a := by
  unfold authElem fragElem at valid
  rw [Heap.singleton_op_singleton (M := LedgerMap)] at valid
  exact Auth.auth_both_valid_discrete.mp ((Heap.singleton_valid_iff (M := LedgerMap)).mp valid)

theorem ref_inclusion c r f rc c' r' (sub : lelem c' r' ≼ lelemc c r f rc) : r' ≤ r := by
  have h := ((Prod.inc_def.mp (Prod.inc_def.mp sub).1).1)
  exact (nat_add_included _ _).mp (Prod.inc_def.mp h).2

theorem refc_inclusion c r f rc (sub : lelemc none 0 none 1 ≼ lelemc c r f rc) : 1 ≤ rc :=
  (nat_add_included _ _).mp (Prod.inc_def.mp sub).2

theorem optional_exclusive_inclusion {A : Type} (cell : Option (Excl (DiscreteO A))) (v : A)
    (valid : ✓ cell) (sub : some (.excl ⟨v⟩) ≼ cell) : cell = some (.excl ⟨v⟩) := by
  obtain ⟨rest, same⟩ := sub
  cases rest with
  | none => exact same.trans (Option.op_none_right_id _)
  | some rest =>
    rw [same] at valid
    exact False.elim valid

theorem claim_inclusion c r f rc ty t q (valid : ✓ lelemc c r f rc)
    (sub : lelem (claimCell ty t q) 0 ≼ lelemc c r f rc) : c = claimCell ty t q := by
  apply optional_exclusive_inclusion c (ty, t, q) valid.1.1.1
  exact (Prod.inc_def.mp (Prod.inc_def.mp (Prod.inc_def.mp sub).1).1).1

theorem freeze_inclusion c r f rc phase (valid : ✓ lelemc c r f rc)
    (sub : lelemf none 0 (freezeCell phase) ≼ lelemc c r f rc) : f = freezeCell phase := by
  apply optional_exclusive_inclusion f phase valid.1.2
  exact (Prod.inc_def.mp (Prod.inc_def.mp sub).1).2

theorem freeze_frag_invalid i p p' : ¬ ✓ (fragElem i (lelemf none 0 (freezeCell p)) • fragElem i (lelemf none 0 (freezeCell p'))) := by
  intro valid
  unfold fragElem at valid
  rw [Heap.singleton_op_singleton (M := LedgerMap), ← Auth.frag_op] at valid
  have values := Auth.frag_valid.mp ((Heap.singleton_valid_iff (M := LedgerMap)).mp valid)
  exact values.1.2

theorem claim_frag_invalid i ty t q ty' t' q' : ¬ ✓ (fragElem i (lelem (claimCell ty t q) 0) • fragElem i (lelem (claimCell ty' t' q') 0)) := by
  intro valid
  unfold fragElem at valid
  rw [Heap.singleton_op_singleton (M := LedgerMap), ← Auth.frag_op] at valid
  have values := Auth.frag_valid.mp ((Heap.singleton_valid_iff (M := LedgerMap)).mp valid)
  exact values.1.1.1

theorem lelem_unit : lelem none 0 = UCMRA.unit := rfl

theorem lelemc_local_update ac ar af arc bc br bf brc ac' ar' arc' bc' br' brc'
    (hc : (ac, bc) ~l~> (ac', bc'))
    (hr : ((⟨ar⟩ : NatAdd), ⟨br⟩) ~l~> (⟨ar'⟩, ⟨br'⟩))
    (hrc : ((⟨arc⟩ : NatAdd), ⟨brc⟩) ~l~> (⟨arc'⟩, ⟨brc'⟩)) :
    (lelemc ac ar af arc, lelemc bc br bf brc) ~l~>
      (lelemc ac' ar' af arc', lelemc bc' br' bf brc') :=
  LocalUpdate.prod' (LocalUpdate.prod' (LocalUpdate.prod' hc hr) (.id _)) hrc

theorem map_update_alloc i a a' b' (update : (a, lelem none 0) ~l~> (a', b')) :
    authElem i a ~~> authElem i a' • fragElem i b' := by
  unfold authElem fragElem
  rw [Heap.singleton_op_singleton (M := LedgerMap)]
  exact Heap.singleton_update (M := LedgerMap) (Auth.auth_update_alloc update)

theorem map_update i a b a' b' (update : (a, b) ~l~> (a', b')) :
    authElem i a • fragElem i b ~~> authElem i a' • fragElem i b' := by
  unfold authElem fragElem
  rw [Heap.singleton_op_singleton (M := LedgerMap), Heap.singleton_op_singleton (M := LedgerMap)]
  exact Heap.singleton_update (M := LedgerMap) (Auth.auth_update update)

end MachCSL.Logic.IcacheRefLedger
