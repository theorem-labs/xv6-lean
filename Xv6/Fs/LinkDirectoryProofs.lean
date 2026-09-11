import Xv6.Fs.LinkSupplyProofs

/-! FsDurImg §9e: first-winner directory views are included in the exact
ticket-list supply after deleting the caller's separately covered name. -/
namespace Xv6.Fs.LinkDirectory
open LinkFamily LinkSupply MachCSL.Logic.FsLink Iris Iris.CMRA Iris.Algebra

abbrev NameFamily (V : Type) := Std.ExtTreeMap FName V

noncomputable def mapOps (self : Int) (orphan : Bool) (types : FName → IType)
    (entries : NameMap) : FamilyRA :=
  bigOpM (M' := NameFamily) CMRA.op
    (fun name target => entryElem self orphan name target (types name)) entries

theorem name_insert_bridge (entries : NameMap) name target :
    Iris.Std.insert (M := NameFamily) entries name target = entries.insert name target := by
  apply Std.ExtTreeMap.ext_getElem?
  intro key
  simp [Iris.Std.insert, Std.ExtTreeMap.getElem?_alter, Std.ExtTreeMap.getElem?_insert]

theorem name_erase_bridge (entries : NameMap) name :
    Iris.Std.delete (M := NameFamily) entries name = entries.erase name := by
  apply Std.ExtTreeMap.ext_getElem?
  intro key
  simp [Iris.Std.delete, Std.ExtTreeMap.getElem?_alter, Std.ExtTreeMap.getElem?_erase]

theorem mapOps_empty self orphan types : mapOps self orphan types ∅ = unit :=
  BigOpM.bigOpM_empty _

theorem mapOps_insert self orphan types (entries : NameMap) name target
    (fresh : entries[name]? = none) :
    mapOps self orphan types (entries.insert name target) =
      entryElem self orphan name target (types name) • mapOps self orphan types entries := by
  simpa only [mapOps, name_insert_bridge] using
    BigOpM.bigOpM_insert_eq (M' := NameFamily) (op := CMRA.op)
      (fun s t => entryElem self orphan s t (types s)) (m := entries) (i := name) target fresh

theorem mapOps_extract self orphan types (entries : NameMap) name target
    (found : entries[name]? = some target) :
    mapOps self orphan types entries =
      entryElem self orphan name target (types name) • mapOps self orphan types (entries.erase name) := by
  simpa only [mapOps, name_erase_bridge] using
    BigOpM.bigOpM_delete_eq (M' := NameFamily) (op := CMRA.op)
      (fun s t => entryElem self orphan s t (types s)) (m := entries) (i := name) (x := target) found

theorem erase_insert_same (entries : NameMap) name target :
    (entries.insert name target).erase name = entries.erase name := by
  apply Std.ExtTreeMap.ext_getElem?
  intro key
  simp only [Std.ExtTreeMap.getElem?_erase, Std.ExtTreeMap.getElem?_insert]
  split <;> simp_all

theorem erase_insert_other (entries : NameMap) name excluded target (different : name ≠ excluded) :
    (entries.insert name target).erase excluded = (entries.erase excluded).insert name target := by
  apply Std.ExtTreeMap.ext_getElem?
  intro key
  simp only [Std.ExtTreeMap.getElem?_erase, Std.ExtTreeMap.getElem?_insert,
    Std.compare_eq_eq_iff_eq]
  by_cases a : excluded = key <;> by_cases b : name = key <;> simp_all

theorem dirView_succ data n : dirView data (n + 1) =
    if dirWins data n then (dirView data n).insert (dirBname data n) (dirInum data n).toNat
    else dirView data n := by
  cases wins : dirWins data n
  · apply Std.ExtTreeMap.ext_getElem?
    intro key
    simp only [wins, Bool.false_eq_true, ↓reduceIte, dirView_succ_lookup, Bool.false_and]
    cases (dirView data n)[key]? <;> rfl
  · have fresh : (dirView data n)[dirBname data n]? = none :=
      (dirView_lookup_none _ _ _).mpr ((dirWins_true data n).mp wins).2
    apply Std.ExtTreeMap.ext_getElem?
    intro key
    simp only [wins, ↓reduceIte, dirView_succ_lookup, Bool.true_and,
      Std.ExtTreeMap.getElem?_insert, Std.compare_eq_eq_iff_eq]
    by_cases same : dirBname data n = key
    · subst key
      simp [fresh]
    · simp only [same, ↓reduceIte, beq_eq_false_iff_ne.mpr same, Bool.false_eq_true]
      cases (dirView data n)[key]? <;> rfl

/-- Exact source premise: only winning, nonexempt, token-bearing records
must provide a ticket and the corresponding target type. -/
theorem view_ops_incl (data : FileData) (self : Int) (orphan : Bool)
    (tick : Nat → Option Int) (values : Int → IType) (types : FName → IType)
    (excluded : FName) (n : Nat)
    (matchTicket : ∀ k, k < n → dirWins data k = true → dirBname data k ≠ excluded →
      tokenless self orphan (dirBname data k) (dirInum data k).toNat = false →
      tick k = some ((dirInum data k).toNat : Int) ∧ types (dirBname data k) = values (dirInum data k).toNat) :
    mapOps self orphan types ((dirView data n).erase excluded) ≼
      tokens values ((List.range n).filterMap tick) := by
  induction n with
  | zero =>
    have empty : dirView data 0 = ∅ := rfl
    rw [empty, Std.ExtTreeMap.erase_empty, mapOps_empty]
    exact CMRA.inc_unit
  | succ n ih =>
    have prior := ih (by intro k bound; exact matchTicket k (by omega))
    rw [List.range_succ, List.filterMap_append, tokens_append, dirView_succ]
    cases wins : dirWins data n
    · rw [if_neg Bool.false_ne_true]
      exact prior.trans (CMRA.inc_op_left _ _)
    · rw [if_pos rfl]
      by_cases exempt : dirBname data n = excluded
      · rw [exempt, erase_insert_same]
        exact prior.trans (CMRA.inc_op_left _ _)
      · rw [erase_insert_other _ _ _ _ exempt]
        have fresh : ((dirView data n).erase excluded)[dirBname data n]? = none := by
          rw [Std.ExtTreeMap.getElem?_erase]
          split
          · rfl
          · exact (dirView_lookup_none _ _ _).mpr ((dirWins_true data n).mp wins).2
        rw [mapOps_insert _ _ _ _ _ _ fresh, CMRA.comm]
        apply CMRA.op_mono prior
        cases ticket : tokenless self orphan (dirBname data n) (dirInum data n).toNat
        · obtain ⟨emitted, typeEq⟩ := matchTicket n (by omega) wins exempt ticket
          rw [List.filterMap_cons, emitted]
          simp only [List.filterMap_nil]
          rw [tokens_singleton, entryElem_ticket _ _ _ _ _ ticket, typeEq]
        · rw [entryElem_exempt _ _ _ _ _ ticket]
          exact CMRA.inc_unit

theorem view_ops_incl_tickets (image : Blocks) (self : Int) (dn : Dinode)
    (orphan : Bool) (values : Int → IType) (types : FName → IType)
    (typeMatch : ∀ k, k < dirNrec dn.sizeZ → dirWins (dataOf image dn) k = true →
      dirBname (dataOf image dn) k ≠ dotName →
      tokenless self orphan (dirBname (dataOf image dn) k) (dirInum (dataOf image dn) k).toNat = false →
      types (dirBname (dataOf image dn) k) = values (dirInum (dataOf image dn) k).toNat) :
    mapOps self orphan types ((dirView (dataOf image dn) (dirNrec dn.sizeZ)).erase dotName) ≼
      tokens values (dirTickets image self dn) := by
  apply view_ops_incl
  intro k bound wins ndot ticket
  refine ⟨?_, typeMatch k bound wins ndot ticket⟩
  apply (recTicket_some image self dn k _).mpr
  exact ⟨((dirWins_true _ _).mp wins).1,
    tokenless_nondot_target self _ orphan _ ndot ticket, rfl⟩

end Xv6.Fs.LinkDirectory

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "Xv6.Fs.LinkDirectory." ||
        name.toString.startsWith "_private.Xv6.Fs.LinkDirectory" then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} link-directory declarations; standard foundational axioms only."
