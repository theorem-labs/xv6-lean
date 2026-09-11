import MachCSL.Logic.ReservationSpec

namespace MachCSL.Logic.Reservations
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI MachCSL.Machine
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap

theorem mapCpus_lookup (f : CPU → Value) (cpus : List CPU) (cpu : CPU) :
    get? (mapCpus f cpus) cpu = if cpu ∈ cpus then some (f cpu) else none := by
  induction cpus with
  | nil => simp [mapCpus, get?_empty]
  | cons c rest ih =>
    simp only [mapCpus, get?_insert, List.mem_cons]
    by_cases he : c = cpu
    · subst c; simp
    · rw [if_neg he, ih]
      simp [Ne.symm he]

theorem resvMap_lookup (f : CPU → Value) (cpu : CPU) :
    get? (resvMap f) cpu = some (f cpu) := by
  rw [resvMap, mapCpus_lookup, if_pos (List.mem_finRange cpu)]

theorem resvMap_insert (f : CPU → Value) (cpu : CPU) (value : Value) :
    resvMap (updateHart f cpu value) = insert (resvMap f) cpu value := by
  apply equiv_iff_eq.mp
  intro other
  rw [resvMap_lookup, get?_insert]
  unfold updateHart
  by_cases he : cpu = other
  · subst other; simp
  · simp [he, Ne.symm he, resvMap_lookup]

theorem resvMap_none (f : CPU → Value) (none : ∀ cpu, f cpu = none) : resvMap f = noneMap := by
  apply equiv_iff_eq.mp
  intro cpu
  simp [noneMap, resvMap_lookup, none]

theorem resvMap_insert_id (f : CPU → Value) (cpu : CPU) (value : Value)
    (same : f cpu = value) : resvMap (updateHart f cpu value) = resvMap f := by
  apply equiv_iff_eq.mp
  intro other
  rw [resvMap_lookup, resvMap_lookup]
  unfold updateHart
  split
  · subst other; rw [same]
  · rfl

theorem noneMap_lookup (cpu : CPU) : get? noneMap cpu = some none := resvMap_lookup _ _

variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance resvFrag_timeless γ cpu value : Timeless (resvFrag capacity γ cpu value) := by
  letI := capacity.reservations
  unfold resvFrag
  infer_instance

instance resvAuth_timeless γ f : Timeless (resvAuth capacity γ f) := by
  letI := capacity.reservations
  unfold resvAuth
  infer_instance

instance resvAny_timeless γ cpu : Timeless (resvAny capacity γ cpu) := by
  unfold resvAny
  infer_instance

theorem resvAny_intro γ cpu value :
    iprop(⊢ resvFrag capacity γ cpu value -∗ resvAny capacity γ cpu) := by
  unfold resvAny
  iintro H
  iexists value
  iexact H

theorem resvFrag_agree γ f cpu value :
    iprop(⊢ resvAuth capacity γ f -∗ resvFrag capacity γ cpu value -∗ ⌜f cpu = value⌝) := by
  letI := capacity.reservations
  unfold resvAuth resvFrag
  iintro Ha Hf
  ihave %h := ghost_map_lookup $$ Ha Hf
  ipureintro
  rw [resvMap_lookup] at h
  exact Option.some.inj h

theorem resvFrag_update γ f cpu value value' :
    iprop(⊢ resvAuth capacity γ f -∗ resvFrag capacity γ cpu value ==∗
      resvAuth capacity γ (updateHart f cpu value') ∗ resvFrag capacity γ cpu value') := by
  letI := capacity.reservations
  unfold resvAuth resvFrag
  rw [resvMap_insert]
  exact ghost_map_update value'

/-- Preserving a reservation needs no per-hart fragment and no ghost update. -/
theorem resvAuth_preserve γ f cpu value (same : f cpu = value) :
    iprop(resvAuth capacity γ f ⊣⊢ resvAuth capacity γ (updateHart f cpu value)) := by
  unfold resvAuth
  rw [resvMap_insert_id f cpu value same]
  exact .rfl

theorem resv_alloc (f : CPU → Value) :
    iprop(⊢ |==> ∃ γ, resvAuth capacity γ f ∗ allFragments capacity γ f) := by
  letI := capacity.reservations
  exact ghost_map_alloc (resvMap f)

/-- Access to each of the eight cells, retaining a reassembly wand. -/
theorem allFragments_acc γ f cpu :
    iprop(⊢ allFragments capacity γ f -∗ resvFrag capacity γ cpu (f cpu) ∗
      (resvFrag capacity γ cpu (f cpu) -∗ allFragments capacity γ f)) := by
  letI := capacity.reservations
  unfold allFragments resvFrag
  iintro H
  iapply (BigSepM.bigSepM_lookup_acc
    (Φ := fun key value => ghost_map_elem γ (.own 1) key value)
    (resvMap_lookup f cpu)).1 $$ H

theorem resvAny_update γ f cpu value :
    iprop(⊢ resvAuth capacity γ f -∗ resvAny capacity γ cpu ==∗
      resvAuth capacity γ (updateHart f cpu value) ∗ resvFrag capacity γ cpu value) := by
  unfold resvAny
  iintro Ha Hf
  icases Hf with ⟨%old, Hf⟩
  iapply resvFrag_update capacity γ f cpu old value $$ Ha Hf

theorem resvFrag_update_frame γ f cpu old value (P : IProp GF) :
    iprop(⊢ resvAuth capacity γ f ∗ resvFrag capacity γ cpu old ∗ P ==∗
      resvAuth capacity γ (updateHart f cpu value) ∗ resvFrag capacity γ cpu value ∗ P) := by
  iintro ⟨Ha, Hf, HP⟩
  imod resvFrag_update capacity γ f cpu old value $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe

theorem resv_none_alloc :
    iprop(⊢ |==> ∃ γ, resvAuth capacity γ (fun _ => none) ∗
      allFragments capacity γ (fun _ => none)) := resv_alloc capacity _

theorem reservationSpec : ReservationSpec capacity where
  alloc := resv_alloc capacity
  cellAccess := allFragments_acc capacity
  anyIntro := resvAny_intro capacity
  agree := resvFrag_agree capacity
  update := resvFrag_update capacity
  preserve := resvAuth_preserve capacity

end MachCSL.Logic.Reservations
