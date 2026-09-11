import MachCSL.Logic.FsLinkSpec
import Iris.ProofMode

namespace MachCSL.Logic.FsLink
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI
open Iris.Std.MultiSet Iris.Std.LawfulMultiSet Iris.Std.FiniteMultiSet

instance : CMRA.Discrete FamilyRA := Heap.instDiscrete (M := FamilyMap) (K := Int)

theorem reps_zero (ty : IType) : reps 0 ty = ∅ := rfl

theorem reps_succ (n : Nat) (ty : IType) : reps (n + 1) ty = ({ty} : Pile) ⊎ reps n ty := by
  change ListPerm.ofList (List.replicate (n + 1) ty) = ListPerm.ofList ([ty] ++ List.replicate n ty)
  rw [List.replicate_succ]
  rfl

theorem reps_one (ty : IType) : reps 1 ty = ({ty} : Pile) := rfl

theorem reps_size (n : Nat) (ty : IType) : size (reps n ty) = n := by
  change (ListPerm.out (ListPerm.ofList (List.replicate n ty))).length = n
  rw [(ListPerm.out_ofList_perm (List.replicate n ty)).length_eq, List.length_replicate]

theorem reps_add (n m : Nat) (ty : IType) : reps (n + m) ty = reps n ty ⊎ reps m ty := by
  change ListPerm.ofList (List.replicate (n + m) ty) =
    ListPerm.ofList (List.replicate n ty ++ List.replicate m ty)
  rw [List.replicate_append_replicate]

theorem reps_member (n : Nat) (ty x : IType) (h : x ∈ reps n ty) : x = ty := by
  rw [mem_iff_multiplicity_pos, reps, ListPerm.multiplicity_ofList] at h
  have mem := List.count_pos_iff.mp h
  exact (List.mem_replicate.mp mem).2

theorem reps_sub_size (pile : Pile) (n : Nat) (ty : IType) (h : pile ⊆ reps n ty) : size pile ≤ n := by
  have eq := congrArg size (disjUnion_difference_of_subseteq h)
  rw [size_disjUnion, reps_size] at eq
  omega

theorem reps_sub_member (pile : Pile) (n : Nat) (ty x : IType)
    (h : pile ⊆ reps n ty) (member : x ∈ pile) : x = ty := by
  apply reps_member n ty x
  rw [mem_iff_multiplicity_pos] at member ⊢
  have bound := subset_iff.mp h x
  omega

theorem toksElem_add (i : Int) (left right : Pile) :
    toksElem i (left ⊎ right) = toksElem i left • toksElem i right := by
  unfold toksElem
  rw [Heap.singleton_op_singleton (M := FamilyMap)]
  rw [← Auth.frag_op]
  rfl

theorem fullElem_valid (i : Int) (n : Nat) (ty : IType) : ✓ fullElem i n ty := by
  unfold fullElem authElem toksElem
  rw [Heap.singleton_op_singleton (M := FamilyMap)]
  apply (Heap.singleton_valid_iff (M := FamilyMap)).mpr
  exact Auth.auth_both_valid_discrete.mpr ⟨.rfl, trivial⟩

theorem mint_update (i : Int) (n k : Nat) (ty : IType) :
    authElem i n ty ~~> authElem i (n + k) ty • toksElem i (reps k ty) := by
  unfold authElem toksElem
  rw [Heap.singleton_op_singleton (M := FamilyMap)]
  apply Heap.singleton_update (M := FamilyMap)
  apply Auth.auth_update_alloc
  apply LeibnizMultiSet.localUpdate
  rw [disjUnion_empty_right, ← reps_add]

theorem return_update (i : Int) (n k : Nat) (ty : IType) :
    authElem i (n + k) ty • toksElem i (reps k ty) ~~> authElem i n ty := by
  unfold authElem toksElem
  rw [Heap.singleton_op_singleton (M := FamilyMap)]
  apply Heap.singleton_update (M := FamilyMap)
  apply Auth.auth_update_dealloc
  apply LeibnizMultiSet.localUpdate
  rw [disjUnion_empty_right, ← reps_add]

theorem empty_fragment_factor (i : Int) (n : Nat) (ty : IType) :
    authElem i n ty = authElem i n ty • toksElem i ∅ := by
  unfold authElem toksElem
  rw [Heap.singleton_op_singleton (M := FamilyMap)]
  congr 1

theorem authElem_zero_retype (i : Int) (ty ty' : IType) :
    authElem i 0 ty = authElem i 0 ty' := rfl

/-- The empty fragment remains a present key with an empty fragment value. -/
theorem toksElem_empty_not_unit (i : Int) : toksElem i ∅ ≠ (unit : FamilyRA) := by
  intro same
  have lookup := congrArg (fun m : FamilyRA => PartialMap.get? m i) same
  unfold toksElem at lookup
  rw [LawfulPartialMap.get?_singleton_eq rfl] at lookup
  contradiction

theorem family_valid_subset (i : Int) (n : Nat) (ty : IType) (pile : Pile)
    (valid : ✓ (authElem i n ty • toksElem i pile)) : pile ⊆ reps n ty := by
  unfold authElem toksElem at valid
  rw [Heap.singleton_op_singleton (M := FamilyMap)] at valid
  have hv := (Heap.singleton_valid_iff (M := FamilyMap)).mp valid
  exact LeibnizMultiSet.included_iff_subset.mp (Auth.auth_both_valid_discrete.mp hv).1

theorem family_valid_token_agreement (i : Int) (n : Nat) (ty ty' : IType)
    (valid : ✓ (authElem i n ty • tokElem i ty')) : ty' = ty ∧ 1 ≤ n := by
  have sub := family_valid_subset i n ty ({ty'} : Pile) valid
  have member : ty' ∈ ({ty'} : Pile) := mem_singleton_iff.mpr rfl
  exact ⟨reps_sub_member _ n ty ty' sub member,
    by simpa only [size_singleton] using reps_sub_size ({ty'} : Pile) n ty sub⟩

/-- An authority rejects a fragment carrying a different directory parent. -/
theorem mismatched_parent_invalid (i : Int) (n : Nat) (left right : Int) (ne : left ≠ right) :
    ¬ ✓ (authElem i n (.directory left) • tokElem i (.directory right)) := by
  intro valid
  have same := (family_valid_token_agreement i n (.directory left) (.directory right) valid).1
  exact ne (IType.directory.inj same).symm

/-- Zero authority permits no nonempty fragment even when its value matches. -/
theorem zero_fragment_invalid (i : Int) (ty ty' : IType) :
    ¬ ✓ (authElem i 0 ty • tokElem i ty') := by
  intro valid
  have bound := reps_sub_size ({ty'} : Pile) 0 ty (family_valid_subset i 0 ty _ valid)
  rw [size_singleton] at bound
  omega

variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance auth_timeless γ i n ty : Timeless (auth capacity γ i n ty) := by unfold auth; infer_instance
instance toks_timeless γ i pile : Timeless (toks capacity γ i pile) := by unfold toks; infer_instance
instance tok_timeless γ i ty : Timeless (tok capacity γ i ty) := by unfold tok; infer_instance

theorem auth_zero_retype γ i ty ty' :
    iprop(auth capacity γ i 0 ty ⊣⊢ auth capacity γ i 0 ty') := by
  unfold auth authElem
  rw [reps_zero ty, reps_zero ty']
  exact .rfl

theorem toks_split γ i (left right : Pile) :
    iprop(toks capacity γ i (left ⊎ right) ⊣⊢ toks capacity γ i left ∗ toks capacity γ i right) := by
  unfold toks
  rw [toksElem_add]
  exact iOwn_op (E := capacity.link)

theorem auth_toks_valid γ i n ty pile :
    iprop(⊢ auth capacity γ i n ty -∗ toks capacity γ i pile -∗ ⌜pile ⊆ reps n ty⌝) := by
  unfold auth toks
  iintro Ha Hf
  icases (iOwn_cmraValid_op (E := capacity.link)) $$ [$Ha $Hf] with %hv
  ipureintro
  unfold authElem toksElem at hv
  rw [Heap.singleton_op_singleton (M := FamilyMap)] at hv
  have hv' := (Heap.singleton_valid_iff (M := FamilyMap)).mp hv
  exact LeibnizMultiSet.included_iff_subset.mp (Auth.auth_both_valid_discrete.mp hv').1

theorem auth_toks_le γ i n ty pile :
    iprop(⊢ auth capacity γ i n ty -∗ toks capacity γ i pile -∗
      ⌜size pile ≤ n ∧ ∀ x, x ∈ pile → x = ty⌝) := by
  iintro Ha Hf
  ihave %sub := auth_toks_valid capacity γ i n ty pile $$ Ha Hf
  ipureintro
  exact ⟨reps_sub_size pile n ty sub, fun x hx => reps_sub_member pile n ty x sub hx⟩

theorem auth_tok_agree γ i n ty ty' :
    iprop(⊢ auth capacity γ i n ty -∗ tok capacity γ i ty' -∗ ⌜ty' = ty ∧ 1 ≤ n⌝) := by
  unfold tok
  iintro Ha Hf
  ihave %law := auth_toks_le capacity γ i n ty ({ty'} : Pile) $$ Ha Hf
  ipureintro
  exact ⟨law.2 ty' (by rw [mem_iff_multiplicity_pos, multiplicity_singleton_eq]; decide), by simpa only [size_singleton] using law.1⟩

theorem auth_zero_no_tok γ i ty ty' :
    iprop(⊢ auth capacity γ i 0 ty -∗ tok capacity γ i ty' -∗ False) := by
  iintro Ha Hf
  ihave %law := auth_tok_agree capacity γ i 0 ty ty' $$ Ha Hf
  ipureintro
  omega

theorem toks_empty γ i n ty :
    iprop(auth capacity γ i n ty ⊣⊢ auth capacity γ i n ty ∗ toks capacity γ i ∅) := by
  unfold auth toks
  have proof := iOwn_op (E := capacity.link) (γ := γ)
    (a1 := authElem i n ty) (a2 := toksElem i ∅)
  rw [← empty_fragment_factor] at proof
  exact proof

theorem mint_reps γ i n k ty :
    iprop(⊢ auth capacity γ i n ty ==∗ auth capacity γ i (n + k) ty ∗ toks capacity γ i (reps k ty)) := by
  unfold auth toks
  iintro Ha
  imod iOwn_update (E := capacity.link) (mint_update i n k ty) $$ Ha with H
  imodintro
  iapply (iOwn_op (E := capacity.link)).mp $$ H

theorem mint γ i n ty :
    iprop(⊢ auth capacity γ i n ty ==∗ auth capacity γ i (n + 1) ty ∗ tok capacity γ i ty) := by
  unfold tok
  exact mint_reps capacity γ i n 1 ty

theorem return_reps γ i n k ty ty' :
    iprop(⊢ auth capacity γ i (n + k) ty -∗ toks capacity γ i (reps k ty') ==∗
      auth capacity γ i n ty) := by
  iintro Ha Ht
  cases k with
  | zero => imodintro; iexact Ha
  | succ k =>
    ihave %sub := auth_toks_valid capacity γ i (n + (k + 1)) ty (reps (k + 1) ty') $$ Ha Ht
    have member : ty' ∈ reps (k + 1) ty' := by
      rw [mem_iff_multiplicity_pos, reps, ListPerm.multiplicity_ofList]
      simp
    have same := reps_sub_member _ (n + (k + 1)) ty ty' sub member
    subst ty'
    unfold auth toks
    iapply iOwn_update_op (E := capacity.link) (return_update i n (k + 1) ty) $$ [$Ha $Ht]

theorem give_back γ i n ty ty' :
    iprop(⊢ auth capacity γ i (n + 1) ty -∗ tok capacity γ i ty' ==∗ auth capacity γ i n ty) := by
  unfold tok
  exact return_reps capacity γ i n 1 ty ty'

theorem family_alloc (family : FamilyRA) (valid : ✓ family) :
    iprop(⊢ |==> ∃ γ, iOwn (E := capacity.link) γ family) :=
  iOwn_alloc (E := capacity.link) family valid

theorem full_split γ i n ty :
    iprop(iOwn (E := capacity.link) γ (fullElem i n ty) ⊣⊢
      auth capacity γ i n ty ∗ toks capacity γ i (reps n ty)) :=
  iOwn_op (E := capacity.link)

theorem full_alloc i n ty :
    iprop(⊢ |==> ∃ γ, auth capacity γ i n ty ∗ toks capacity γ i (reps n ty)) := by
  imod family_alloc capacity (fullElem i n ty) (fullElem_valid i n ty) with ⟨%γ, H⟩
  imodintro
  iexists γ
  iapply (full_split capacity γ i n ty).mp $$ H

theorem toks_reps_succ γ i n ty :
    iprop(toks capacity γ i (reps (n + 1) ty) ⊣⊢
      tok capacity γ i ty ∗ toks capacity γ i (reps n ty)) := by
  rw [reps_succ]
  exact toks_split capacity γ i _ _

theorem toks_le_split γ i n k ty (bound : k ≤ n) :
    iprop(toks capacity γ i (reps n ty) ⊢
      toks capacity γ i (reps k ty) ∗ toks capacity γ i (reps (n - k) ty)) := by
  have hn : n = k + (n - k) := by omega
  have he : reps n ty = reps k ty ⊎ reps (n - k) ty := by
    calc reps n ty = reps (k + (n - k)) ty := congrArg (reps · ty) hn
         _ = _ := reps_add _ _ ty
  rw [he]
  exact (toks_split capacity γ i _ _).mp

theorem toks_list_at γ i count ty start :
    iprop(toks capacity γ i (reps count ty) ⊢
      [∗list] _entry ∈ List.range' start count, tok capacity γ i ty) := by
  induction count generalizing start with
  | zero => iintro H; iempintro
  | succ count ih =>
    rw [List.range'_succ, BigSepL.bigSepL_cons.to_eq]
    iintro H
    icases (toks_reps_succ capacity γ i count ty).mp $$ H with ⟨Ht, Hs⟩
    isplitl [Ht]
    · iexact Ht
    · iapply ih (start + 1) $$ Hs

theorem toks_list γ i count ty :
    iprop(toks capacity γ i (reps count ty) ⊢
      [∗list] _entry ∈ List.range count, tok capacity γ i ty) := by
  have proof := toks_list_at capacity γ i count ty 0
  simpa only [List.range_eq_range'] using proof

theorem mint_frame γ i n k ty (P : IProp GF) :
    iprop(⊢ auth capacity γ i n ty ∗ P ==∗
      auth capacity γ i (n + k) ty ∗ toks capacity γ i (reps k ty) ∗ P) := by
  iintro ⟨Ha, HP⟩
  imod mint_reps capacity γ i n k ty $$ Ha with ⟨Ha, Ht⟩
  imodintro
  iframe

theorem return_frame γ i n k ty ty' (P : IProp GF) :
    iprop(⊢ auth capacity γ i (n + k) ty ∗ toks capacity γ i (reps k ty') ∗ P ==∗
      auth capacity γ i n ty ∗ P) := by
  iintro ⟨Ha, Ht, HP⟩
  imod return_reps capacity γ i n k ty ty' $$ Ha Ht with Ha
  imodintro
  iframe

theorem fsLinkSpec : FsLinkSpec capacity where
  zeroRetype := auth_zero_retype capacity
  split := toks_split capacity
  valid := auth_toks_valid capacity
  agree := auth_tok_agree capacity
  mint := mint_reps capacity
  giveBack := return_reps capacity
  allocate := family_alloc capacity

end MachCSL.Logic.FsLink
