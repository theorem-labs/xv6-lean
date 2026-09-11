import Xv6.Fs.LinkSupplyDefs
import Xv6.Fs.LinkFamilyProofs
import Lean.Util.CollectAxioms
import Lean.Elab.Command

namespace Xv6.Fs.LinkSupply
open DurableNode LinkFamily MachCSL.Logic.FsLink Iris Iris.CMRA Iris.Algebra
open Iris.Std (PartialMap LawfulPartialMap LawfulFiniteMap)

/-- Singleton folding retains a present element even if that element is empty. -/
theorem singletonFold_lookup (nodes : DurableState.InodeMap) (value : Int → Node → ElementRA)
    (key : Int) :
    PartialMap.get? (M := FamilyMap) (bigOpM (M' := FamilyMap) CMRA.op
      (fun i n => (PartialMap.singleton (M := FamilyMap) i (value i n))) nodes) key =
      (PartialMap.get? (M := FamilyMap) nodes key).map (value key) := by
  induction nodes using LawfulFiniteMap.induction_on (M := FamilyMap) generalizing key with
  | hemp => rw [BigOpM.bigOpM_empty]; rfl
  | hins i n nodes absent ih =>
    rw [BigOpM.bigOpM_insert_eq _ n absent, Heap.get?_op (M := FamilyMap)]
    by_cases same : i = key
    · subst key
      rw [LawfulPartialMap.get?_singleton_eq rfl, LawfulPartialMap.get?_insert_eq rfl,
        ih, absent]
      rfl
    · rw [LawfulPartialMap.get?_singleton_ne same, LawfulPartialMap.get?_insert_ne same, ih]
      exact CMRA.unit_left_id_L

theorem authorities_lookup (nodes : DurableState.InodeMap) values key :
    (authorities nodes values)[key]? = nodes[key]?.map
      (fun n => (● (LeibnizMultiSet.ofSet (reps (multiplicity n) (values key))) : ElementRA)) :=
  singletonFold_lookup nodes _ key

theorem supply_lookup (nodes : DurableState.InodeMap) values key :
    (supply nodes values)[key]? = nodes[key]?.map
      (fun n => (◯ (LeibnizMultiSet.ofSet (reps (multiplicity n) (values key))) : ElementRA)) :=
  singletonFold_lookup nodes _ key

theorem fullMap_split (nodes : DurableState.InodeMap) values :
    fullMap nodes values = authorities nodes values • supply nodes values :=
  BigOpM.bigOpM_op_eq (M' := FamilyMap) (op := CMRA.op) _ _ nodes

theorem elem_split (nodes : DurableState.InodeMap) f :
    elem nodes f = authorities nodes (choiceValue f) • outgoing nodes f :=
  BigOpM.bigOpM_op_eq (M' := FamilyMap) (op := CMRA.op) _ _ nodes

theorem fullMap_lookup (nodes : DurableState.InodeMap) values key :
    (fullMap nodes values)[key]? = nodes[key]?.map
      (fun n => (● (LeibnizMultiSet.ofSet (reps (multiplicity n) (values key))) : ElementRA) •
        (◯ (LeibnizMultiSet.ofSet (reps (multiplicity n) (values key))) : ElementRA)) := by
  rw [fullMap_split]
  change PartialMap.get? (M := FamilyMap) (authorities nodes values • supply nodes values) key = _
  rw [Heap.get?_op (M := FamilyMap)]
  change (authorities nodes values)[key]? • (supply nodes values)[key]? = _
  rw [authorities_lookup, supply_lookup]
  cases nodes[key]? <;> rfl

/-- No node well-formedness or entry-count premise is needed at full ownership. -/
theorem fullMap_valid (nodes : DurableState.InodeMap) values : ✓ fullMap nodes values := by
  intro key
  change ✓ (fullMap nodes values)[key]?
  rw [fullMap_lookup]
  cases nodes[key]? with
  | none => trivial
  | some n => exact Auth.auth_both_valid_discrete.mpr ⟨.rfl, trivial⟩

theorem authorities_valid (nodes : DurableState.InodeMap) values : ✓ authorities nodes values := by
  have valid := fullMap_valid nodes values
  rw [fullMap_split] at valid
  exact CMRA.valid_op_left valid

theorem supply_valid (nodes : DurableState.InodeMap) values : ✓ supply nodes values := by
  have valid := fullMap_valid nodes values
  rw [fullMap_split] at valid
  exact CMRA.valid_op_right _ _ valid

theorem outgoing_no_entries (nodes : DurableState.InodeMap) (f : Choice)
    (empty : ∀ (i : Int) (n : Node), nodes[i]? = some n → n.dirEntries = ∅) : outgoing nodes f = unit := by
  apply Eq.trans (b := bigOpM (M' := FamilyMap) CMRA.op
    (fun (_ : Int) (_ : Node) => (unit : FamilyRA)) nodes)
  · apply BigOpM.bigOpM_eq
    intro i n found
    exact entriesElem_no_entries i n _ (empty i n found)
  · exact BigOpM.bigOpM_const_unit_eq _

theorem elem_valid_no_entries (nodes : DurableState.InodeMap) (f : Choice)
    (empty : ∀ (i : Int) (n : Node), nodes[i]? = some n → n.dirEntries = ∅) : ✓ elem nodes f := by
  rw [elem_split, outgoing_no_entries nodes f empty, CMRA.unit_right_id_L]
  exact authorities_valid nodes _

theorem outgoing_one (nodes : DurableState.InodeMap) (f : Choice) (home : Int) (node : Node)
    (found : nodes[home]? = some node)
    (others : ∀ i n, nodes[i]? = some n → i ≠ home → n.dirEntries = ∅) :
    outgoing nodes f = entriesElem home node (choiceTypes f home) := by
  unfold outgoing
  rw [BigOpM.bigOpM_delete_eq (M' := FamilyMap) (op := CMRA.op) _
    (m := nodes) (i := home) (x := node) found]
  have empty : bigOpM (M' := FamilyMap) CMRA.op
      (fun i n => entriesElem i n (choiceTypes f i)) (PartialMap.delete nodes home) =
        (unit : FamilyRA) := by
    apply Eq.trans (b := bigOpM (M' := FamilyMap) CMRA.op
      (fun (_ : Int) (_ : Node) => (unit : FamilyRA)) (PartialMap.delete (M := FamilyMap) nodes home))
    · apply BigOpM.bigOpM_eq
      intro i n lookup
      have h := Iris.Std.LawfulPartialMap.get?_delete_some_iff.mp lookup
      exact entriesElem_no_entries i n _ (others i n h.2 h.1.symm)
    · exact BigOpM.bigOpM_const_unit_eq _
  rw [empty]
  exact CMRA.unit_right_id_L

/-- Exact source reduction with arbitrary slack, not just a root singleton. -/
theorem elem_valid_of_root (nodes : DurableState.InodeMap) (f : Choice) (home : Int) (node : Node)
    (slack : FamilyRA) (found : nodes[home]? = some node)
    (others : ∀ i n, nodes[i]? = some n → i ≠ home → n.dirEntries = ∅)
    (covered : entriesElem home node (choiceTypes f home) • slack ≼ supply nodes (choiceValue f)) :
    ✓ (elem nodes f • slack) := by
  apply CMRA.valid_of_inc (y := fullMap nodes (choiceValue f)) ?_ (fullMap_valid nodes _)
  rw [fullMap_split, elem_split, outgoing_one nodes f home node found others]
  rw [← CMRA.assoc]
  exact CMRA.op_mono_right _ covered

theorem tokens_nil values : tokens values [] = unit := rfl
theorem tokens_cons values target tickets :
    tokens values (target :: tickets) = tokElem target (values target) • tokens values tickets := rfl
theorem tokens_append values left right :
    tokens values (left ++ right) = tokens values left • tokens values right :=
  BigOpL.bigOpL_append_eq _ left right
theorem tokens_singleton values target : tokens values [target] = tokElem target (values target) :=
  BigOpL.bigOpL_singleton_eq _ target

theorem tickCount_cons (target : Int) tickets key :
    tickCount (target :: tickets) key =
      if target = key then tickCount tickets key + 1 else tickCount tickets key := by
  by_cases same : target = key <;> simp [tickCount, same]

theorem tickCount_append left right key :
    tickCount (left ++ right) key = tickCount left key + tickCount right key := by
  simp [tickCount, List.filter_append]

theorem tickCount_join (lists : List (List Int)) (tickets : List Int) key (member : tickets ∈ lists) :
    tickCount tickets key ≤ tickCount lists.flatten key := by
  induction lists with
  | nil => contradiction
  | cons head tail ih =>
    rw [List.flatten_cons, tickCount_append]
    rcases List.mem_cons.mp member with same | rest
    · subst tickets
      omega
    · have := ih rest
      omega

theorem tickCount_member tickets key (positive : 0 < tickCount tickets key) : key ∈ tickets := by
  by_cases member : key ∈ tickets
  · exact member
  · have zero := tickCount_zero tickets key (by intro t ht same; exact member (same ▸ ht))
    omega

theorem tokens_lookup_zero values tickets key (zero : tickCount tickets key = 0) :
    (tokens values tickets)[key]? = none := by
  induction tickets with
  | nil => rfl
  | cons target rest ih =>
    rw [tickCount_cons] at zero
    have different : target ≠ key := by intro same; simp [same] at zero
    rw [if_neg different] at zero
    rw [tokens_cons]
    change PartialMap.get? (M := FamilyMap) (tokElem target (values target) • tokens values rest) key = _
    rw [Heap.get?_op (M := FamilyMap)]
    have absent : PartialMap.get? (M := FamilyMap) (tokElem target (values target)) key = none :=
      LawfulPartialMap.get?_singleton_ne different
    rw [absent]
    change (none : Option ElementRA) • (tokens values rest)[key]? = _
    rw [ih zero]
    rfl

theorem tokens_lookup_pos values tickets key (positive : 0 < tickCount tickets key) :
    (tokens values tickets)[key]? =
      some (◯ (LeibnizMultiSet.ofSet (reps (tickCount tickets key) (values key))) : ElementRA) := by
  induction tickets with
  | nil => simp [tickCount] at positive
  | cons target rest ih =>
    rw [tokens_cons]
    change PartialMap.get? (M := FamilyMap) (tokElem target (values target) • tokens values rest) key = _
    rw [Heap.get?_op (M := FamilyMap)]
    rw [tickCount_cons] at positive ⊢
    by_cases same : target = key
    · subst target
      rw [if_pos rfl]
      have head : PartialMap.get? (M := FamilyMap) (tokElem key (values key)) key =
          some (◯ (LeibnizMultiSet.ofSet ({values key} : Pile)) : ElementRA) :=
        LawfulPartialMap.get?_singleton_eq rfl
      rw [head]
      change some (◯ (LeibnizMultiSet.ofSet ({values key} : Pile)) : ElementRA) •
        (tokens values rest)[key]? = _
      by_cases zero : tickCount rest key = 0
      · rw [tokens_lookup_zero values rest key zero, zero]
        rfl
      · rw [ih (by omega)]
        change some ((◯ (LeibnizMultiSet.ofSet ({values key} : Pile)) : ElementRA) •
          (◯ (LeibnizMultiSet.ofSet (reps (tickCount rest key) (values key))) : ElementRA)) = _
        rw [← Auth.frag_op, reps_succ]
        rfl
    · rw [if_neg same] at positive ⊢
      have absent : PartialMap.get? (M := FamilyMap) (tokElem target (values target)) key = none :=
        LawfulPartialMap.get?_singleton_ne same
      rw [absent]
      change (none : Option ElementRA) • (tokens values rest)[key]? = _
      rw [ih positive]
      rfl

theorem tokens_lookup values tickets key :
    (tokens values tickets)[key]? = if tickCount tickets key = 0 then none else
      some (◯ (LeibnizMultiSet.ofSet (reps (tickCount tickets key) (values key))) : ElementRA) := by
  by_cases zero : tickCount tickets key = 0
  · rw [if_pos zero, tokens_lookup_zero values tickets key zero]
  · rw [if_neg zero, tokens_lookup_pos values tickets key (by omega)]

theorem reps_included (small large : Nat) (ty : IType) (bound : small ≤ large) :
    LeibnizMultiSet.ofSet (reps small ty) ≼ LeibnizMultiSet.ofSet (reps large ty) := by
  refine ⟨LeibnizMultiSet.ofSet (reps (large - small) ty), ?_⟩
  have sum : small + (large - small) = large := by omega
  have counts := reps_add small (large - small) ty
  rw [sum] at counts
  rw [counts]
  rfl

/-- Source list-count inclusion, with no premise on keys absent from the list. -/
theorem tokens_included_supply values tickets (nodes : DurableState.InodeMap)
    (covered : ∀ key, 0 < tickCount tickets key →
      ∃ n, nodes[key]? = some n ∧ tickCount tickets key ≤ multiplicity n) :
    tokens values tickets ≼ supply nodes values := by
  apply (Heap.lookup_inc (M := FamilyMap)).mpr
  intro key
  change (tokens values tickets)[key]? ≼ (supply nodes values)[key]?
  by_cases zero : tickCount tickets key = 0
  · rw [tokens_lookup_zero values tickets key zero]
    exact CMRA.inc_unit
  · obtain ⟨n, found, bound⟩ := covered key (by omega)
    rw [tokens_lookup_pos values tickets key (by omega), supply_lookup, found]
    exact Iris.Option.some_inc_some_of_inc
      (Auth.frag_inc_of_inc (reps_included _ _ _ bound))

/-- Empty ticket lists have no key, even where the family has a zero supply. -/
theorem supply_zero_present (nodes : DurableState.InodeMap) values (key : Int) n
    (found : nodes[key]? = some n) (zero : multiplicity n = 0) :
    (supply nodes values)[key]? = some (◯ (LeibnizMultiSet.ofSet (∅ : Pile)) : ElementRA) := by
  rw [supply_lookup, found]
  simp only [Option.map_some, zero, reps_zero]

theorem supply_zero_not_empty (nodes : DurableState.InodeMap) values (key : Int) n
    (found : nodes[key]? = some n) (zero : multiplicity n = 0) :
    supply nodes values ≠ tokens values [] := by
  intro same
  have lookup := congrArg (fun m : FamilyRA => m[key]?) same
  rw [supply_zero_present nodes values key n found zero] at lookup
  contradiction

/-- Repeated tickets preserve multiplicity rather than collapsing to a set. -/
theorem repeated_ticket_lookup values key :
    (tokens values [key, key])[key]? =
      some (◯ (LeibnizMultiSet.ofSet (reps 2 (values key))) : ElementRA) := by
  have count : tickCount [key, key] key = 2 := by simp [tickCount]
  rw [tokens_lookup_pos values [key, key] key (by omega), count]

theorem unmatched_ticket_absent values (left right : Int) (different : left ≠ right) :
    (tokens values [left, left])[right]? = none := by
  apply tokens_lookup_zero
  simp [tickCount, different]

theorem tokens_empty_included_supply values (nodes : DurableState.InodeMap) :
    tokens values [] ≼ supply nodes values := CMRA.inc_unit

end Xv6.Fs.LinkSupply

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "Xv6.Fs.LinkSupply." ||
        name.toString.startsWith "_private.Xv6.Fs.LinkSupply" then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} link-supply declarations; standard foundational axioms only."
