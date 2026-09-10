import MachCSL.Machine.Observations

/-! Per-power-cycle reading of the interleaved history, `ObsTrace.v` section 5. -/
namespace MachCSL.Machine

def cycleStep (cycles : List (List Observation)) : Observation → List (List Observation)
  | .powerOn => [] :: cycles
  | .powerOff => cycles
  | event => match cycles with
    | [] => [[event]]
    | current :: rest => (current ++ [event]) :: rest

def cyclesReverse (history : List Observation) : List (List Observation) :=
  history.foldl cycleStep []

def cyclesOf (history : List Observation) : List (List Observation) := (cyclesReverse history).reverse

theorem cyclesReverse_append (history events : List Observation) :
    cyclesReverse (history ++ events) = events.foldl cycleStep (cyclesReverse history) := by
  simp [cyclesReverse, List.foldl_append]

theorem traceShape_cycles (history : List Observation) (shape : TraceShape history true) :
    ∃ rest, cyclesReverse history = openSegment history :: rest := by
  induction history using FromMathlib.List.reverseRec with
  | nil => simp [TraceShape] at shape
  | append_singleton history event ih =>
    unfold TraceShape at shape
    rw [List.foldl_append] at shape
    cases hs : history.foldl observationStep (some false) with
    | none => cases event <;> simp [hs, observationStep] at shape
    | some on =>
      cases on with
      | false =>
        cases event <;> simp [hs, observationStep] at shape
        exact ⟨cyclesReverse history, by simp [cyclesReverse_append, openSegment_append, cycleStep, segmentStep]⟩
      | true =>
        obtain ⟨rest, hr⟩ := ih hs
        cases event <;> simp [hs, observationStep] at shape
        all_goals exact ⟨rest, by simp [cyclesReverse_append, hr, openSegment_append, cycleStep, segmentStep]⟩

theorem cyclesOf_on (history : List Observation) :
    cyclesOf (history ++ [.powerOn]) = cyclesOf history ++ [[]] := by
  simp [cyclesOf, cyclesReverse_append, cycleStep]

theorem cyclesOf_off (history : List Observation) :
    cyclesOf (history ++ [.powerOff]) = cyclesOf history := by
  simp [cyclesOf, cyclesReverse_append, cycleStep]

theorem cycleStep_io (current : List Observation) (rest : List (List Observation))
    (events : List Observation) (io : ∀ e ∈ events, isIO e = true) :
    events.foldl cycleStep (current :: rest) = (current ++ events) :: rest := by
  induction events generalizing current with
  | nil => simp
  | cons e events ih =>
    have he := io e (by simp)
    have hr : ∀ x ∈ events, isIO x = true := fun x hx => io x (by simp [hx])
    cases e <;> simp_all [isIO, cycleStep, List.append_assoc]

theorem cyclesOf_io (history events : List Observation) (shape : TraceShape history true)
    (io : ∀ e ∈ events, isIO e = true) :
    ∃ completed, cyclesOf history = completed ++ [openSegment history] ∧
      cyclesOf (history ++ events) = completed ++ [openSegment history ++ events] := by
  obtain ⟨rest, hr⟩ := traceShape_cycles history shape
  refine ⟨rest.reverse, ?_, ?_⟩
  · simp [cyclesOf, hr]
  · simp [cyclesOf, cyclesReverse_append, hr, cycleStep_io _ _ _ io]

end MachCSL.Machine
