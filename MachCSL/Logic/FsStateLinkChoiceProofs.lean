import MachCSL.Logic.FsStateLinkDefs
import Iris.ProofMode

namespace MachCSL.Logic.FsState
open Iris Iris.Std Iris.BI Xv6.Fs FsView

/-- Finite dependent choices assembled into a total function. Values outside
the input map are arbitrary, and no separation resource is duplicated. -/
theorem map_choose {GF : BundledGFunctors} {K V C : Type} {M : Type → Type}
    [LawfulFiniteMap M K] [DecidableEq K] (fallback : C)
    (P : K → V → C → Prop) (Q : K → V → C → IProp GF) (m : M V) :
    bigSepM (M := M) (fun k v => iprop(∃ c, ⌜P k v c⌝ ∗ Q k v c)) m ⊢
      iprop(∃ f : K → C, ⌜∀ k v, PartialMap.get? m k = some v → P k v (f k)⌝ ∗
        bigSepM (M := M) (fun k v => Q k v (f k)) m) := by
  induction m using LawfulFiniteMap.induction_on (M := M) with
  | hemp =>
    iintro _
    iexists (fun _ => fallback)
    isplit
    · ipureintro; intro k v h; rw [LawfulPartialMap.get?_empty] at h; cases h
    · iapply (BigSepM.bigSepM_empty (M := M)).mpr
      iempintro
  | hins k v m absent ih =>
    rw [BigSepM.bigSepM_insert absent |>.to_eq]
    iintro ⟨⟨%c, %pc, Hc⟩, Hrest⟩
    ihave ⟨%f, %pf, Hrest⟩ := ih $$ Hrest
    let f' : K → C := fun key => if key = k then c else f key
    have agrees key value (found : PartialMap.get? m key = some value) : f' key = f key := by
      have ne : key ≠ k := by intro eq; subst key; rw [absent] at found; cases found
      simp [f', ne]
    iexists f'
    isplit
    · ipureintro
      intro key value found
      by_cases eq : key = k
      · subst key
        rw [LawfulPartialMap.get?_insert_eq rfl] at found
        cases found
        simpa [f'] using pc
      · rw [LawfulPartialMap.get?_insert_ne (Ne.symm eq)] at found
        rw [agrees key value found]
        exact pf key value found
    · rw [BigSepM.bigSepM_insert absent |>.to_eq]
      isplitl [Hc]
      · rw [show f' k = c by simp [f']]
        iexact Hc
      · iapply BigSepM.bigSepM_mono (M := M) (Φ := fun key value => Q key value (f key))
        · intro key value found
          rw [agrees key value found]
        · iexact Hrest

end MachCSL.Logic.FsState
