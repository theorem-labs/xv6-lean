import MachCSL.Logic.TsoDefs

/-! Source `TsoMemPa.pin_ok_author:2343–2370`. The proof raises the read view
to an already-visible anchor. Newly visible older messages are shadowed by
that anchor, so the byte chosen by the descending scan does not change. -/
namespace MachCSL.Logic.TsoPinnedRead
open MachCSL.Memory

theorem visible_raise_above (h view floor : Nat) (log : WriteLog width) (time : Nat)
    (above : floor < time) : visible h (max view floor) log time = visible h view log time := by
  have eq : (time ≤ max view floor) ↔ time ≤ view := by omega
  simp only [visible, eq]

theorem readDown_raise_anchor (image : ByteMap width) (log : WriteLog width)
    (h view : Nat) (a : Address width) (position : Nat) (byte : Byte)
    (seen : visible h view log position = true)
    (value : logByte image log position a = some byte) (n : Nat) (inside : position ≤ n) :
    readDown image log h view a n = readDown image log h (max view position) a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases last : position = n + 1
    · subst position
      have seen' := visible_mono h view (max view (n + 1)) log (n + 1)
        (Nat.le_max_left _ _) seen
      simp [readDown, seen, seen', value]
    · have above : position < n + 1 := by omega
      rw [readDown, readDown, visible_raise_above h view position log (n + 1) above]
      split
      · rfl
      · exact ih (by omega)

/-- No current-view lower bound: the visible authored anchor suffices. -/
theorem pinOK_author (image : ByteMap 64) (log : WriteLog 64)
    (a : PhysicalAddress) (bound position : Nat) (byte : Byte) (allowed : Tso.ByteSet)
    (h : Agent) (pin : Tso.PinOK image log a bound allowed) (floor : bound ≤ position)
    (seen : ∀ view, visible h view log position = true)
    (value : logByte image log position a = some byte) :
    ∀ view, ∃ v, read image log h view a = some v ∧ v ∈ allowed := by
  intro view
  obtain ⟨v, result, member⟩ := pin h (max view position) (by omega)
  refine ⟨v, ?_, member⟩
  change readDown image log h view a log.length = some v
  rw [readDown_raise_anchor image log h view a position byte (seen view) value log.length
    (logByte_some_le image log position a byte value)]
  exact result

end MachCSL.Logic.TsoPinnedRead
