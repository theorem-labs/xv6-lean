import MachCSL.Logic.FsBlockGhostSpec

namespace MachCSL.Logic.FsBlockGhost
open Iris Iris.Std Iris.BI
open scoped MachCSL.Logic.FsBlockGhost.Key
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance cacheAuth_timeless names cache : Timeless (cacheAuth capacity names cache) := by
  letI := capacity.cache
  unfold cacheAuth
  infer_instance
instance dirtyAuth_timeless names dirty : Timeless (dirtyAuth capacity names dirty) := by
  letI := capacity.dirty
  unfold dirtyAuth
  infer_instance
instance cacheElem_timeless names dq b bytes : Timeless (cacheElem capacity names dq b bytes) := by
  letI := capacity.cache
  unfold cacheElem
  infer_instance
instance dirtyElem_timeless names dq b value : Timeless (dirtyElem capacity names dq b value) := by
  letI := capacity.dirty
  unfold dirtyElem
  infer_instance
instance chalf_timeless names b bytes : Timeless (chalf capacity names b bytes) := by unfold chalf; infer_instance
instance dirtyHalf_timeless names b value : Timeless (dirtyHalf capacity names b value) := by unfold dirtyHalf; infer_instance
instance mclean_timeless names b bytes : Timeless (mclean capacity names b bytes) := by unfold mclean; infer_instance
instance mdirty_timeless names b bytes : Timeless (mdirty capacity names b bytes) := by unfold mdirty; infer_instance
instance exc_auth_timeless g X : Timeless (exc_auth capacity g X) := by
  letI := capacity.exceptions
  unfold exc_auth
  infer_instance
instance exc_own_timeless g X : Timeless (exc_own capacity g X) := by
  letI := capacity.exceptions
  unfold exc_own
  infer_instance
instance exc_sealed_timeless g : Timeless (exc_sealed capacity g) := by
  letI := capacity.exceptions
  unfold exc_sealed
  infer_instance
instance exc_sealed_persistent g : Persistent (exc_sealed capacity g) := by
  letI := capacity.exceptions
  unfold exc_sealed
  infer_instance

theorem clean_agree names b bytes machinery :
    iprop(⊢ chalf capacity names b bytes -∗ mclean capacity names b machinery -∗ ⌜machinery = bytes⌝) := by
  letI := capacity.cache
  unfold mclean chalf cacheElem
  iintro Hc ⟨Hm, _⟩
  iapply ghost_map_elem_agree names.cache b (.own (1 : Qp).half) (.own (1 : Qp).half) machinery bytes
  iframe

theorem dirty_agree names b bytes machinery :
    iprop(⊢ chalf capacity names b bytes -∗ mdirty capacity names b machinery -∗ ⌜machinery = bytes⌝) := by
  letI := capacity.cache
  unfold mdirty chalf cacheElem
  iintro Hc ⟨Hm, _⟩
  iapply ghost_map_elem_agree names.cache b (.own (1 : Qp).half) (.own (1 : Qp).half) machinery bytes
  iframe

private theorem halves_update {V : Type} [GhostMapG GF Int V BlockMap]
    (g : GName) (map : BlockMap V) (b : Int) (value new other : V) :
    iprop(⊢ (ghost_map_auth g (.own 1) map : IProp GF) -∗
      ghost_map_elem g (.own (1 : Qp).half) b value -∗
      ghost_map_elem g (.own (1 : Qp).half) b other ==∗
      ⌜other = value ∧ get? map b = some value⌝ ∗
      ghost_map_auth g (.own 1) (PartialMap.insert map b new) ∗
      ghost_map_elem g (.own (1 : Qp).half) b new ∗
      ghost_map_elem g (.own (1 : Qp).half) b new) := by
  have split (v : V) : iprop((ghost_map_elem g (.own 1) b v : IProp GF) ⊣⊢
      ghost_map_elem g (.own (1 : Qp).half) b v ∗ ghost_map_elem g (.own (1 : Qp).half) b v) := by
    simpa only [Qp.half_add_half] using
      (Fractional.fractional (Φ := fun q : Qp => (ghost_map_elem g (.own q) b v : IProp GF))
        (1 : Qp).half (1 : Qp).half)
  iintro Ha Hc Hm
  ihave %eq := ghost_map_elem_agree g b (.own (1 : Qp).half) (.own (1 : Qp).half) other value $$ [$Hm $Hc]
  subst other
  ihave He := (split value).mpr $$ [$Hc $Hm]
  ihave %found := ghost_map_lookup $$ Ha He
  imod ghost_map_update new $$ Ha He with ⟨Ha, He⟩
  ihave ⟨Hc, Hm⟩ := (split new).mp $$ He
  imodintro
  iframe Ha Hc Hm
  ipureintro
  exact ⟨rfl, found⟩

theorem cache_update names cache b bytes new machinery :
    iprop(⊢ cacheAuth capacity names cache -∗ chalf capacity names b bytes -∗
      chalf capacity names b machinery ==∗
      ⌜machinery = bytes ∧ get? cache b = some bytes⌝ ∗
      cacheAuth capacity names (PartialMap.insert cache b new) ∗
      chalf capacity names b new ∗ chalf capacity names b new) := by
  letI := capacity.cache
  exact halves_update names.cache cache b bytes new machinery

theorem dirty_flip names dirty b value other new :
    iprop(⊢ dirtyAuth capacity names dirty -∗ dirtyHalf capacity names b value -∗
      dirtyHalf capacity names b other ==∗
      ⌜other = value ∧ get? dirty b = some value⌝ ∗
      dirtyAuth capacity names (PartialMap.insert dirty b new) ∗
      dirtyHalf capacity names b new ∗ dirtyHalf capacity names b new) := by
  letI := capacity.dirty
  exact halves_update names.dirty dirty b value new other

theorem exception_allocate (X : ExceptionSet) (frame : IProp GF) :
    iprop(frame ⊢ |==> ∃ g, exc_auth capacity g X ∗ exc_own capacity g X ∗ frame) := by
  letI := capacity.exceptions
  iintro Hframe
  imod ghost_map_alloc (PartialMap.singleton () X : ExceptionMap ExceptionSet) with ⟨%g, Ha, Hf⟩
  ihave Hf := BigSepM.bigSepM_singleton.mp $$ Hf
  imodintro
  iexists g
  unfold exc_auth exc_own
  iframe

theorem exception_agree g left right :
    iprop(⊢ exc_auth capacity g left -∗ exc_own capacity g right -∗ ⌜left = right⌝) := by
  letI := capacity.exceptions
  unfold exc_auth exc_own
  iintro Ha Hf
  ihave %found := ghost_map_lookup $$ Ha Hf
  ipureintro
  simpa only [LawfulPartialMap.get?_singleton_eq rfl, Option.some.injEq] using found

theorem sealed_empty g X :
    iprop(⊢ exc_auth capacity g X -∗ exc_sealed capacity g -∗ ⌜X = ∅⌝) := by
  letI := capacity.exceptions
  unfold exc_auth exc_sealed
  iintro Ha Hf
  ihave %found := ghost_map_lookup $$ Ha Hf
  ipureintro
  simpa only [LawfulPartialMap.get?_singleton_eq rfl, Option.some.injEq] using found

theorem exception_update g old new :
    iprop(⊢ exc_auth capacity g old -∗ exc_own capacity g old ==∗
      exc_auth capacity g new ∗ exc_own capacity g new) := by
  letI := capacity.exceptions
  unfold exc_auth exc_own
  iintro Ha Hf
  imod ghost_map_update new $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  isimp only [PartialMap.singleton, LawfulPartialMap.insert_insert_same] at Ha
  unfold PartialMap.singleton
  iframe

theorem exception_seal g : iprop(exc_own capacity g ∅ ⊢ |==> exc_sealed capacity g) := by
  letI := capacity.exceptions
  unfold exc_own exc_sealed
  iintro Hf
  iapply ghost_map_elem_persist (GF := GF) (H := ExceptionMap) g () (.own 1) (∅ : ExceptionSet) $$ Hf

theorem actual : Spec capacity :=
  ⟨clean_agree capacity, dirty_agree capacity, cache_update capacity, dirty_flip capacity,
    exception_allocate capacity, exception_agree capacity, sealed_empty capacity,
    exception_update capacity, exception_seal capacity⟩

end MachCSL.Logic.FsBlockGhost
