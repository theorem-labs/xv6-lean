import MachCSL.Logic.JalBootResourcesDefs

namespace MachCSL.Logic.JalBootResources
open Iris Iris.Std Iris.BI MachCSL.Memory
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap

/-- Remove exactly the selected cells; every other full resource is retained. -/
def deleteKeys (m : Tso.AddressMap V) : List PhysicalAddress → Tso.AddressMap V
  | [] => m
  | a :: rest => deleteKeys (delete m a) rest

theorem extract_keys {GF : BundledGFunctors} (Φ : PhysicalAddress → V → IProp GF)
    (keys : List PhysicalAddress) (unique : keys.Nodup) (values : PhysicalAddress → V)
    (m : Tso.AddressMap V) (lookup : ∀ a, a ∈ keys → get? m a = some (values a)) :
    iprop(⊢ ([∗map] a ↦ value ∈ m, Φ a value) -∗
      ([∗list] a ∈ keys, Φ a (values a)) ∗
      ([∗map] a ↦ value ∈ deleteKeys m keys, Φ a value)) := by
  induction keys generalizing m with
  | nil =>
    simp only [deleteKeys]
    iintro H
    isplitl []
    · iapply BigSepL.bigSepL_nil.mpr; itrivial
    · iexact H
  | cons a rest ih =>
    obtain ⟨absent, nodup⟩ := List.nodup_cons.mp unique
    have found := lookup a (by simp)
    have tail : ∀ b, b ∈ rest → get? (delete m a) b = some (values b) := by
      intro b member
      have different : a ≠ b := by intro eq; subst b; exact absent member
      rw [get?_delete_ne different]
      exact lookup b (by simp [member])
    iintro H
    ihave ⟨Ha, Hrest⟩ := (BigSepM.bigSepM_delete found).1 $$ H
    ihave ⟨Hkeys, Hrest⟩ := ih nodup (delete m a) tail $$ Hrest
    simp only [deleteKeys]
    iapply (sep_mono_left BigSepL.bigSepL_cons.mpr)
    iframe

end MachCSL.Logic.JalBootResources
