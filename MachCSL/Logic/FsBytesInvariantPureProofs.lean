import MachCSL.Logic.FsBytesInvariantSpec
import MachCSL.Logic.FsDurBytesProofs

namespace MachCSL.Logic.FsBytesInvariant
open Iris Iris.Std

theorem fsbN_logN : (↑fsbN : CoPset) ⊆ ↑logN := nclose_subseteq logN ("b" : String)
theorem fsbN_sub (E : CoPset) (mask : (↑logN : CoPset) ⊆ E) : (↑fsbN : CoPset) ⊆ E :=
  fun _ member => mask _ (fsbN_logN _ member)

theorem bytes_tie_exc_empty logged cache : bytes_tie_exc logged cache ∅ ↔ bytes_tie logged cache := by
  constructor
  · intro h b bs found
    exact h b bs found (by simp)
  · intro h b bs found _
    exact h b bs found

theorem byte_runs_agree (start : Int) (left right : List Byte) (logged : ByteMap)
    (length : left.length = right.length)
    (hl : PartialMap.submap (FsDurBytes.byteRun start left) logged)
    (hr : PartialMap.submap (FsDurBytes.byteRun start right) logged) : left = right := by
  apply List.ext_getElem length
  intro k hk hk'
  have getL : get? (FsDurBytes.byteRun start left) (start + (k : Int)) = some left[k] :=
    (FsDurBytes.byteRun_lookup start _ left left[k]).mpr ⟨k, List.getElem?_eq_getElem hk, rfl⟩
  have getR : get? (FsDurBytes.byteRun start right) (start + (k : Int)) = some right[k] :=
    (FsDurBytes.byteRun_lookup start _ right right[k]).mpr ⟨k, List.getElem?_eq_getElem hk', rfl⟩
  exact Option.some.inj ((hl _ _ getL).symm.trans (hr _ _ getR))

theorem range_home_pure (logged : ByteMap) (home : BlockSet) (block : Int) (offset : Nat) (bytes : List Byte)
    (domain : bytes_dom logged home) (off : offset < 1024) (nonempty : 0 < bytes.length)
    (included : PartialMap.submap (FsDurBytes.byteRun (block * 1024 + (offset : Int)) bytes) logged) : block ∈ home := by
  cases bytes with
  | nil => simp at nonempty
  | cons first rest =>
    have found : get? (FsDurBytes.byteRun (block * 1024 + (offset : Int)) (first :: rest))
        (block * 1024 + (offset : Int)) = some first :=
      (FsDurBytes.byteRun_lookup _ _ _ _).mpr ⟨0, rfl, by simp⟩
    have existsByte : (get? logged (block * 1024 + (offset : Int))).isSome := by
      rw [included _ _ found]
      rfl
    obtain ⟨other, member, lo, hi⟩ := (domain _).mp existsByte
    have same : block = other := by omega
    simpa only [same] using member

theorem cache_home_lookup (cache : CacheMap) (home : BlockSet) (block : Int)
    (domain : FiniteMap.dom_set (S := BlockSet) cache = home) (member : block ∈ home) :
    ∃ bytes, get? cache block = some bytes := by
  apply Option.isSome_iff_exists.mp
  apply (LawfulFiniteMap.mem_dom_set (S := BlockSet) (m := cache)).mp
  simpa only [domain] using member

end MachCSL.Logic.FsBytesInvariant
