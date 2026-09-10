import MachCSL.Sail.Interface

/-!
Finite, event-labeled execution of the existing free V1 tree. Every single step
requires an explicit dependent handler fact; there is no administrative or
unconditional stutter step. A trace records both the request and its typed result,
with intermediate states witnessed by its step derivation.

The handler is a parameter, not an assertion that a RISC-V machine has been
implemented. These compositional laws do not supply a hardware handler, a CPU
loop, interleaving semantics, or Iris/MachCSL adequacy.
-/
namespace MachCSL.Sail.Execution

open _root_.Sail.ArchSem (FreeM)
open _root_.Sail.ConcurrencyInterfaceV1.Free

variable {Register : Type} {RegisterType : Register → Type}
variable [_root_.Sail.ConcurrencyInterfaceV1.Arch] {ue : Type}
variable {State : Type} {α β : Type}

/-- The event and its dependent result are retained together. -/
abbrev Observation (RegisterType : Register → Type) (ue : Type) :=
  (event : Event RegisterType ue) × event.Result

/-- The machine must define which request/result/state transitions are allowed. -/
abbrev Handler (RegisterType : Register → Type) (ue State : Type) :=
  (event : Event RegisterType ue) → State → event.Result → State → Prop

/-- Exactly one handled event advances the continuation with the recorded result. -/
inductive Step (H : Handler RegisterType ue State) :
    (PreSailM RegisterType ue α × State) → Observation RegisterType ue →
    (PreSailM RegisterType ue α × State) → Prop where
  | event {request : Event RegisterType ue} {result : request.Result}
      {continuation : request.Result → PreSailM RegisterType ue α} {before after : State}
      (handled : H request before result after) :
      Step H (.impure request continuation, before) ⟨request, result⟩
        (continuation result, after)

/-- A finite sequence of actual event steps. `nil` means zero steps. -/
inductive Steps (H : Handler RegisterType ue State) :
    (PreSailM RegisterType ue α × State) → List (Observation RegisterType ue) →
    (PreSailM RegisterType ue α × State) → Prop where
  | nil (configuration) : Steps H configuration [] configuration
  | cons {first middle last} {observation trace}
      (step : Step H first observation middle)
      (rest : Steps H middle trace last) : Steps H first (observation :: trace) last

variable {H : Handler RegisterType ue State}

/-- Inversion exposes the same request, result, final state and continuation. -/
theorem step_impure_iff {request : Event RegisterType ue}
    {continuation : request.Result → PreSailM RegisterType ue α}
    {result : request.Result} {before after : State} {next : PreSailM RegisterType ue α} :
    Step H (.impure request continuation, before) ⟨request, result⟩ (next, after) ↔
      H request before result after ∧ next = continuation result := by
  constructor
  · intro h
    cases h with
    | event handled => exact ⟨handled, rfl⟩
  · rintro ⟨handled, rfl⟩
    exact .event handled

/-- Pure return is terminal, rather than an unconditionally stuttering step. -/
theorem no_step_pure (value : α) (state : State) (observation) (next) :
    ¬ Step H (.pure value, state) observation next := by
  intro step
  cases step

/-- An Empty-result event cannot resume, independently of the handler relation. -/
theorem no_step_empty {request : Event RegisterType ue}
    (empty : request.Result → Empty) (continuation : request.Result → PreSailM RegisterType ue α)
    (state : State) (observation) (next) :
    ¬ Step H (.impure request continuation, state) observation next := by
  intro step
  cases step
  exact (empty ‹request.Result›).elim

/-- Sail errors have Empty results and therefore no execution step. -/
theorem no_step_error (error : _root_.Sail.Error ue) (state : State) (observation)
    (next : PreSailM RegisterType ue α × State) :
    ¬ Step H (fail error, state) observation next :=
  no_step_empty (H := H) (request := .error error) id Empty.elim state observation next

/-- Discard has an Empty result and cannot be interpreted as a silent return. -/
theorem no_step_discard (state : State) (observation)
    (next : PreSailM RegisterType ue α × State) :
    ¬ Step H (PreSail.sail_discard (), state) observation next :=
  no_step_empty (H := H) (request := .discard) id Empty.elim state observation next

/-- An unhandled request has no step, even when its result type is inhabited. -/
theorem no_step_unhandled {request : Event RegisterType ue}
    (continuation : request.Result → PreSailM RegisterType ue α) (state : State)
    (unhandled : ∀ result after, ¬ H request state result after) (observation) (next) :
    ¬ Step H (.impure request continuation, state) observation next := by
  intro step
  cases step with
  | event handled => exact unhandled _ _ handled

/-- Binding adds no event and preserves the handled result and both endpoint states. -/
theorem Step.bind {first last : PreSailM RegisterType ue α × State} {observation}
    (step : Step H first observation last) (f : α → PreSailM RegisterType ue β) :
    Step H (first.1 >>= f, first.2) observation (last.1 >>= f, last.2) := by
  cases step with
  | event handled => exact .event handled

/-- Binding preserves an entire prefix trace, including its exact order and results. -/
theorem Steps.bind {first last : PreSailM RegisterType ue α × State} {trace}
    (run : Steps H first trace last) (f : α → PreSailM RegisterType ue β) :
    Steps H (first.1 >>= f, first.2) trace (last.1 >>= f, last.2) := by
  induction run with
  | nil => exact .nil _
  | cons step _ ih => exact .cons (step.bind f) ih

/-- Adjacent executions concatenate their event traces without dropping steps. -/
theorem Steps.append {first middle last : PreSailM RegisterType ue α × State}
    {beforeTrace afterTrace} (left : Steps H first beforeTrace middle) (right : Steps H middle afterTrace last) :
    Steps H first (beforeTrace ++ afterTrace) last := by
  induction left with
  | nil => exact right
  | cons step _ ih => exact .cons step (ih right)

/-- A terminating left computation composes with its continuation at the same state. -/
theorem Steps.bind_append {computation : PreSailM RegisterType ue α}
    {f : α → PreSailM RegisterType ue β} {value : α} {before middle : State}
    {last : PreSailM RegisterType ue β × State} {beforeTrace afterTrace}
    (left : Steps H (computation, before) beforeTrace (.pure value, middle))
    (right : Steps H (f value, middle) afterTrace last) :
    Steps H (computation >>= f, before) (beforeTrace ++ afterTrace) last :=
  (left.bind f).append right

/-- All terminating bind executions split at the left return, preserving the full
trace and the intermediate machine state. There is no determinism assumption. -/
theorem completes_bind_iff {computation : PreSailM RegisterType ue α}
    {f : α → PreSailM RegisterType ue β} {value : β} {before after : State} {trace} :
    Steps H (computation >>= f, before) trace (.pure value, after) ↔
      ∃ leftValue middle beforeTrace afterTrace,
        trace = beforeTrace ++ afterTrace ∧
        Steps H (computation, before) beforeTrace (.pure leftValue, middle) ∧
        Steps H (f leftValue, middle) afterTrace (.pure value, after) := by
  constructor
  · intro run
    induction computation generalizing before trace with
    | pure leftValue =>
      exact ⟨leftValue, before, [], trace, rfl, .nil _, run⟩
    | impure request continuation ih =>
      cases run with
      | cons step rest =>
        cases step with
        | event handled =>
          obtain ⟨leftValue, middle, beforeTrace, afterTrace, eqTrace, left, right⟩ := ih _ rest
          exact ⟨leftValue, middle, _ :: beforeTrace, afterTrace,
            congrArg (_ :: ·) eqTrace, .cons (.event handled) left, right⟩
  · rintro ⟨leftValue, middle, beforeTrace, afterTrace, rfl, left, right⟩
    exact left.bind_append right

/-- A trace beginning at a pure value must be the empty execution at that state. -/
theorem steps_pure_iff {value : α} {state : State} {trace} {last} :
    Steps H (.pure value, state) trace last ↔ trace = [] ∧ last = (.pure value, state) := by
  constructor
  · intro run
    cases run with
    | nil => exact ⟨rfl, rfl⟩
    | cons step _ => exact (no_step_pure _ _ _ _ step).elim
  · rintro ⟨rfl, rfl⟩
    exact .nil _

end MachCSL.Sail.Execution
