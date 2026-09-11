import Xv6.Fs.BitmapProofs

/-! Abstract assembly lemmas keep concrete readers opaque during certificate linking. -/
namespace Xv6.Fs

theorem collectNodup_getD (xs : List Int) (ok : (collectNodup xs).isSome = true) :
    collectNodup xs = some ((collectNodup xs).getD ∅) := by
  cases h : collectNodup xs with
  | none => simp [h] at ok
  | some s => rfl

theorem blocksBitmapValid_of_collected image sb used
    (collected : usedSet image sb = some used)
    (valid : bitmapValid image sb used = true) : blocksBitmapValid image sb = true := by
  unfold blocksBitmapValid
  rw [collected]
  exact valid

end Xv6.Fs
