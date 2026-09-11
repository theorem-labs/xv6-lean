import MachCSL.Logic.LockRankDefs

namespace MachCSL.Logic.LockRank
open Iris.Std Iris.Std.LawfulSet

theorem rank_proc : rank "proc" = 9 := rfl
theorem rank_kmem : rank "kmem" = 11 := rfl

theorem lookup_absent (entries : List (String × Nat)) (name : String)
    (absent : ∀ entry ∈ entries, entry.1 ≠ name) : lookup entries name = 0 := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨key, value⟩
    have different : name ≠ key := Ne.symm (absent (key, value) (by simp))
    simp only [lookup, beq_iff_eq, different, ↓reduceIte]
    exact ih (fun entry member => absent entry (by simp [member]))

theorem rank_default (name : String)
    (absent : ∀ entry ∈ ranks, entry.1 ≠ name) : rank name = 0 :=
  lookup_absent ranks name absent

theorem below_empty name : Below ∅ name := by
  intro other member
  exact (mem_empty member).elim

theorem below_not_mem {held : Names} {name : String} (below : Below held name) :
    name ∉ held := fun member => Nat.lt_irrefl _ (below name member)

theorem below_add {held : Names} {name next : String}
    (less : rank name < rank next) (below : Below held next) : Below ({name} ∪ held) next := by
  intro other member
  rcases mem_union.mp member with member | member
  · exact (mem_singleton.mp member) ▸ less
  · exact below other member

theorem below_mono {held : Names} {name next : String}
    (below : Below held name) (le : rank name ≤ rank next) : Below held next := by
  intro other member
  exact Nat.lt_of_lt_of_le (below other member) le

theorem below_difference {held removed : Names} {name : String}
    (below : Below held name) : Below (held \ removed) name :=
  fun other member => below other (mem_diff.mp member).1

theorem add_delete (name : String) (held : Names) (absent : name ∉ held) :
    ({name} ∪ held) \ {name} = held := by
  apply LawfulSet.ext
  intro other
  simp only [mem_diff, mem_union, mem_singleton]
  constructor
  · rintro ⟨same | member, different⟩
    · exact (different same).elim
    · exact member
  · intro member
    exact ⟨.inr member, fun same => absent (same ▸ member)⟩

theorem delete_eq_erase (name : String) (held : Names) :
    held \ {name} = held.erase name := by
  apply _root_.Std.ExtTreeSet.ext_mem
  intro other
  simp [mem_diff, _root_.Std.ExtTreeSet.mem_erase, and_comm]

theorem size_add (name : String) (held : Names) (absent : name ∉ held) :
    ({name} ∪ held).size = held.size + 1 := by
  rw [← insert_eq_singleton_union_extTreeSet]
  simp [_root_.Std.ExtTreeSet.size_insert, absent]

theorem size_delete (name : String) (held : Names) :
    (held \ {name}).size ≤ held.size := _root_.Std.ExtTreeSet.size_diff_le_size_left

theorem size_delete_lt (name : String) (held : Names) (n : Nat)
    (member : name ∈ held) (bound : held.size ≤ n + 1) :
    (held \ {name}).size ≤ n := by
  rw [delete_eq_erase]
  have contains : held.contains name = true := by simpa using member
  simp only [_root_.Std.ExtTreeSet.size_erase, contains, ↓reduceIte]
  omega

theorem size_le_zero_empty (held : Names) (bound : held.size ≤ 0) : held = ∅ :=
  _root_.Std.ExtTreeSet.eq_empty_iff_size_eq_zero.mpr (Nat.eq_zero_of_le_zero bound)

theorem size_empty_le (n : Nat) : (∅ : Names).size ≤ n := by
  simp [_root_.Std.ExtTreeSet.size_empty]

theorem size_add_le (name : String) (held : Names) (n : Nat)
    (absent : name ∉ held) (bound : held.size ≤ n) : ({name} ∪ held).size ≤ n + 1 := by
  rw [size_add name held absent]
  omega

theorem size_delete_le (name : String) (held : Names) (n : Nat)
    (bound : held.size ≤ n) : (held \ {name}).size ≤ n :=
  Nat.le_trans (size_delete name held) bound

theorem self_delete (name : String) : ({name} : Names) \ {name} = ∅ := by
  apply LawfulSet.ext
  intro other
  simp

theorem union_empty (name : String) : ({name} : Names) ∪ ∅ = {name} := union_empty_right

theorem empty_delete (removed : Names) : (∅ : Names) \ removed = ∅ := by
  apply LawfulSet.ext
  intro other
  simp [mem_diff]

theorem add_delete_below (name : String) (held : Names) (below : Below held name) :
    ({name} ∪ held) \ {name} = held := add_delete name held (below_not_mem below)

theorem below_singleton {name next : String} (less : rank name < rank next) :
    Below {name} next := by
  intro other member
  exact (mem_singleton.mp member) ▸ less

end MachCSL.Logic.LockRank
