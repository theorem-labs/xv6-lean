import Iris.Std.GenSetsInstances

/-! Exact name-keyed order from `LockRank.v`. Finite sets contain arbitrary
strings; the concrete rank table does not restrict their carrier. -/
namespace MachCSL.Logic.LockRank

abbrev Names := _root_.Std.ExtTreeSet String

def ranks : List (String × Nat) :=
  [("log", 1), ("bcache", 2), ("cons", 3), ("sleep lock", 4),
   ("pipe", 5), ("time", 6), ("virtio_disk", 7), ("wait_lock", 8),
   ("proc", 9), ("nextpid", 10), ("kmem", 11), ("itable", 14),
   ("ftable", 15), ("pr", 16), ("uart", 17)]

def lookup : List (String × Nat) → String → Nat
  | [], _ => 0
  | (name, rank) :: rest, target => if target == name then rank else lookup rest target

def rank (name : String) : Nat := lookup ranks name

def Below (held : Names) (name : String) : Prop :=
  ∀ other, other ∈ held → rank other < rank name

instance belowDecidable (held : Names) (name : String) : Decidable (Below held name) :=
  decidable_of_iff (∀ other ∈ held.toList, rank other < rank name) (by
    simp only [_root_.Std.ExtTreeSet.mem_toList]
    rfl)

end MachCSL.Logic.LockRank
