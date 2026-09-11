import MachCSL.Logic.FsBytesBootstrapGrowProofs
import MachCSL.Logic.FsBytesInvariantRowsProofs

namespace MachCSL.Logic.FsBytesBootstrap
open Iris Iris.Std Iris.BI
open FsDurBytes FsBytesInvariant
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF)

theorem fs_bytes_alloc (names : Names) (cache : BlockMap) (values : Int → List Byte) (exceptions : BlockSet)
    (full : BlocksFull cache)
    (valueFull : ∀ b, b ∈ FiniteMap.dom_set (S := BlockSet) cache → (values b).length = 1024)
    (exceptionHome : exceptions ⊆ FiniteMap.dom_set (S := BlockSet) cache)
    (agreement : ∀ b bytes, get? cache b = some bytes → b ∉ exceptions → values b = bytes)
    (E : CoPset) (frame : IProp GF) :
    iprop(⊢ cacheHalves capacity names cache -∗ frame ={E}=∗ ∃ gL gX,
      invariant capacity (withBytes names gL gX) (FiniteMap.dom_set (S := BlockSet) cache) values ∗
      FsBlockGhost.exc_own capacity.blocks gX exceptions ∗
      committedRuns capacity gL cache values ∗ frame) := by
  letI := capacity.bytes.image
  iintro HC Hframe
  imod (ghost_map_alloc_empty (H := Disk.ImageMap) (K := Int) (V := Byte)) with ⟨%gL, Ha⟩
  have grow := byte_map_grow capacity gL (valueMap cache values) ∅ ∅
    (valueMap_full cache values valueFull) (by intro b _; simp) empty_domain frame
  unfold Disk.mapAuth at grow
  imod grow $$ Ha Hframe
    with ⟨%logged, %domain, %tie, Ha, Hblocks, Hframe⟩
  have domain' : bytes_dom logged (FiniteMap.dom_set (S := BlockSet) cache) := by
    simpa only [LawfulSet.union_empty_left, valueMap_domain] using domain
  have lookup (b : Int) (bs : List Byte) (found : get? cache b = some bs) :
      get? (valueMap cache values) b = some (values b) := by rw [valueMap_lookup, found]; rfl
  have tie' : bytes_tie_exc logged cache exceptions := by
    intro b bs found outside
    rw [← agreement b bs found outside]
    exact tie b (values b) (lookup b bs found)
  have exceptionValues : bytes_exc_val logged values exceptions := by
    intro b member
    obtain ⟨bs, found⟩ := Option.isSome_iff_exists.mp (LawfulFiniteMap.mem_dom_set.mp (exceptionHome b member))
    exact tie b (values b) (lookup b bs found)
  imod FsBlockGhost.exception_allocate capacity.blocks exceptions frame $$ Hframe
    with ⟨%gX, Hxa, Hxo, Hframe⟩
  imod inv_alloc fsbN E (body capacity (withBytes names gL gX)
    (FiniteMap.dom_set (S := BlockSet) cache) values) $$ [Ha HC Hxa] with Hi
  · iintro !>
    iapply body_intro capacity (withBytes names gL gX) logged cache exceptions
      (FiniteMap.dom_set (S := BlockSet) cache) values rfl full tie' domain' exceptionHome exceptionValues
    unfold withBytes cacheHalves Disk.mapAuth
    iframe
    unfold FsBlockGhost.chalf FsBlockGhost.cacheElem
    iexact HC
  · imodintro
    iexists gL, gX
    unfold invariant
    iframe Hi Hxo Hframe
    iapply (valueMap_runs capacity gL cache values).mp
    iexact Hblocks

end MachCSL.Logic.FsBytesBootstrap
