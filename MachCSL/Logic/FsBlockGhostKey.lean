import Std.Data.ExtTreeMap

/-! Scoped lawful order for the exact source Unit exception-map key.
Only one key exists; no numeric surrogate or extra map entries are introduced. -/
namespace MachCSL.Logic.FsBlockGhost.Key

scoped instance unitOrd : Ord Unit where
  compare _ _ := .eq

open scoped MachCSL.Logic.FsBlockGhost.Key

scoped instance unitTransOrd : Std.TransOrd Unit where
  eq_swap := by intros; rfl
  isLE_trans := by intros; rfl

scoped instance unitLawfulEqOrd : Std.LawfulEqOrd Unit where
  compare_self := by intros; rfl
  eq_of_compare := by intros a b _; cases a; cases b; rfl

end MachCSL.Logic.FsBlockGhost.Key
