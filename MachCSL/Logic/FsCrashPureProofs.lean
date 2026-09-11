import MachCSL.Logic.FsCrashSpec

namespace MachCSL.Logic.FsCrash
open Iris Iris.Std Iris.Algebra

theorem record_history_nonempty record physical covered start
    (wf : RecordWF record physical covered start) : record.history ≠ [] := by
  intro empty
  have last := wf.last
  rw [empty] at last
  cases last

theorem historyEmbed_prefix (pre history : List BlockMap) :
    historyEmbed pre <+: historyEmbed history ↔ pre <+: history := by
  constructor
  · intro h
    have plain := h.map DiscreteO.car
    simpa [historyEmbed, List.map_map, Function.comp_def] using plain
  · intro h
    exact h.map DiscreteO.mk

theorem history_last_split record physical covered start (wf : RecordWF record physical covered start) :
    ∃ pre, record.history = pre ++ [record.committed] := List.getLast?_eq_some_iff.mp wf.last

theorem mirrorOf_ok physical covered start : MirrorOK (mirrorOf physical) physical covered start := by
  intro b _; rfl

theorem mirrorUpdate_same mirror block bytes : (mirrorUpdate mirror block bytes).view block = bytes := by
  simp [mirrorUpdate]
theorem mirrorUpdate_other mirror block other bytes (different : other ≠ block) :
    (mirrorUpdate mirror block bytes).view other = mirror.view other := by simp [mirrorUpdate, different]

end MachCSL.Logic.FsCrash
