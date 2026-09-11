import Xv6.Kernel.KptOwnershipSlotProofs

set_option maxRecDepth 10000

namespace Xv6.Kernel.KptOwnership
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

/-- Exact list-position cut, with every other cell retained behind the wand. -/
theorem bundle_access {GF : BundledGFunctors} {V : Type} (P : Index → V → IProp GF)
    (values : Index → V) (i : Index) :
    iprop((bigSepL (fun _ j => P j (values j)) indices) ⊢ P i (values i) ∗
      (∀ value, P i value -∗ bigSepL
        (fun _ j => P j (if j = i then value else values j)) indices)) := by
  have found := index_lookup i
  iintro H
  ihave ⟨Hi,Hrest⟩ := (BigSepL.bigSepL_delete_cond (PROP := IProp GF) (A := Index) (l := indices) (i := i.toNat) (x := i) (Φ := fun _ j => P j (values j)) found).mp $$ H
  iframe Hi
  iintro %value Hi
  iapply (BigSepL.bigSepL_delete_cond (PROP := IProp GF) (A := Index) (l := indices) (i := i.toNat) (x := i) (Φ := fun _ j => P j (if j = i then value else values j)) found).mpr
  isplitl [Hi]
  · isimp only [ite_true]
    iexact Hi
  · iapply BigSepL.bigSepL_mono $$ Hrest
    intro k j hj
    by_cases same : k = i.toNat
    · simp only [same, ite_true]
      exact .rfl
    · have different : j ≠ i := by
        intro eq
        subst j
        exact same (index_lookup_position k i hj)
      simp only [if_neg same, if_neg different]
      exact .rfl

variable {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)

theorem page_access_ro tier dq t i : iprop(pageOwn capacity era tier dq t ⊢
    slotOwn capacity era tier (PtTree.slotAddress (PtTree.base t) i) dq (PtTree.entries t i) ∗
    (slotOwn capacity era tier (PtTree.slotAddress (PtTree.base t) i) dq (PtTree.entries t i) -∗
      pageOwn capacity era tier dq t)) := by
  unfold pageOwn
  iintro ⟨#Hclaim,Hslots⟩
  ihave ⟨Hi,Hrest⟩ := BigSepL.bigSepL_mem_acc (PROP := IProp GF) (A := Index) (l := indices) (x := i) (Φ := fun j =>
    slotOwn capacity era tier (PtTree.slotAddress (PtTree.base t) j) dq (PtTree.entries t j)) (List.mem_of_getElem? (index_lookup i)) $$ Hslots
  iframe Hi
  iintro Hi
  iframe Hclaim
  iapply Hrest $$ Hi

theorem page_access tier dq t i : iprop(pageOwn capacity era tier dq t ⊢
    slotOwn capacity era tier (PtTree.slotAddress (PtTree.base t) i) dq (PtTree.entries t i) ∗
    (∀ w', slotOwn capacity era tier (PtTree.slotAddress (PtTree.base t) i) dq w' -∗
      pageOwn capacity era tier dq (PtTree.updateEntry t i w'))) := by
  unfold pageOwn
  iintro ⟨#Hclaim,Hslots⟩
  ihave ⟨Hi,Hrest⟩ := bundle_access
    (fun j word => slotOwn capacity era tier (PtTree.slotAddress (PtTree.base t) j) dq word)
    (PtTree.entries t) i $$ Hslots
  iframe Hi
  iintro %w' Hi
  isimp only [PtTree.base_updateEntry, PtTree.entries_updateEntry]
  iframe Hclaim
  iapply Hrest $$ Hi

theorem page_update_child tier dq t i c :
    pageOwn capacity era tier dq (PtTree.updateChild t i c) = pageOwn capacity era tier dq t := by
  unfold pageOwn
  rw [PtTree.base_updateChild, PtTree.entries_updateChild]

theorem kids_update_entry tier depth dq t i w :
    kidsOwn capacity era tier depth dq (PtTree.updateEntry t i w) = kidsOwn capacity era tier depth dq t := by
  unfold kidsOwn
  rw [PtTree.children_updateEntry]

theorem tree_succ tier depth dq t : treeOwn capacity era tier (depth + 1) dq t =
    iprop(pageOwn capacity era tier dq t ∗ kidsOwn capacity era tier depth dq t) := rfl

theorem tree_zero tier dq t : treeOwn capacity era tier 0 dq t = iprop(pageOwn capacity era tier dq t ∗ emp) := rfl

theorem kids_access_ro tier depth dq t i c (child : PtTree.children t i = some c) :
    iprop(kidsOwn capacity era tier depth dq t ⊢ treeOwn capacity era tier depth dq c ∗
      (treeOwn capacity era tier depth dq c -∗ kidsOwn capacity era tier depth dq t)) := by
  unfold kidsOwn
  iintro H
  ihave ⟨Hi,Hrest⟩ := BigSepL.bigSepL_mem_acc (PROP := IProp GF) (A := Index) (l := indices) (x := i) (Φ := fun j => match PtTree.children t j with
    | none => iprop(emp)
    | some c => treeOwn capacity era tier depth dq c) (List.mem_of_getElem? (index_lookup i)) $$ H
  isimp only [child] at Hi Hrest
  iframe Hi
  iintro Hi
  iapply Hrest $$ Hi

theorem kids_access tier depth dq t i c (child : PtTree.children t i = some c) :
    iprop(kidsOwn capacity era tier depth dq t ⊢ treeOwn capacity era tier depth dq c ∗
      (∀ c', treeOwn capacity era tier depth dq c' -∗
        kidsOwn capacity era tier depth dq (PtTree.updateChild t i (some c')))) := by
  unfold kidsOwn
  iintro H
  ihave ⟨Hi,Hrest⟩ := bundle_access
    (fun _ maybeChild => match maybeChild with
      | none => emp
      | some c => treeOwn capacity era tier depth dq c) (PtTree.children t) i $$ H
  isimp only [child] at Hi
  iframe Hi
  iintro %c' Hi
  isimp only [PtTree.children_updateChild]
  ispecialize Hrest $$ %(some c')
  iapply Hrest $$ Hi

end Xv6.Kernel.KptOwnership
