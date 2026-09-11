import MachCSL.Machine.SpinlockPoolReplaceProofs

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.EventPlan Logic.SpinlockProtocol

/-- Every actual node permitted by the protocol plan retains devices and
preserves code. Its write request is forced to the exact lock/counter payload
by the proved mode eligibility, including all metadata and size. -/
theorem head_node_scenery [Platform] {i : Fin 17} {rs : RegisterFile} {rr : Option Reservation}
    {phase : Phase} {program program' : SailM Unit} {Q}
    {s s' : LocalState Devices.State} {others : PhysicalAddress → Prop} {hart : Agent}
    {image : ByteMap 64}
    (head : EventPlanHead.Head (SpinlockFetch.CodeRead i) relations rs rr phase program Q)
    (code : SpinlockCodeIntegrity.CodeUnwritten s.log)
    (node : NodeStep Devices.bus others hart image s program program' s') :
    s'.devices = s.devices ∧ SpinlockCodeIntegrity.CodeUnwritten s'.log := by
  cases head with
  | pure good => obtain ⟨tick, _, rfl⟩ := node; exact ⟨rfl, code⟩
  | readOwned owned rest => obtain ⟨_, rfl⟩ := node; exact ⟨rfl, code⟩
  | readPin pin rest => obtain ⟨_, rfl⟩ := node; exact ⟨rfl, code⟩
  | writeOwned owned rest => obtain ⟨_, rfl⟩ := node; exact ⟨rfl, code⟩
  | barrier enabled rest => obtain ⟨_, rfl⟩ := node; exact ⟨rfl, code⟩
  | codeRead ram plain allowed rest =>
    simp only [NodeStep, ram, plain, Bool.false_eq_true, ↓reduceIte, true_and, false_and, or_false] at node
    obtain ⟨view, word, _, _, _, _, rfl⟩ := node
    exact ⟨rfl, code⟩
  | plain enabled ram kind rest =>
    simp only [NodeStep, ram, kind, Bool.false_eq_true, ↓reduceIte, true_and, false_and, or_false] at node
    obtain ⟨view, word, _, _, _, _, rfl⟩ := node
    exact ⟨rfl, code⟩
  | exclusive enabled ram kind rest =>
    simp only [NodeStep, ram, kind, Bool.true_eq_false, true_and, false_and, false_or] at node
    rcases node with ⟨_, _, rfl⟩ | ⟨_, word, _, _, rfl⟩ <;> exact ⟨rfl, code⟩
  | write enabled present ram mode eligible rest =>
    simp only [NodeStep, present, ram, Bool.false_eq_true, ↓reduceIte] at node
    rcases node with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
    · exact ⟨rfl, code⟩
    · refine ⟨rfl, ?_⟩
      cases eligible with
      | swap old bound => exact SpinlockCodeIntegrity.append_data s.log code _ (Or.inl rfl) _ hart
      | increment B v t rr => exact SpinlockCodeIntegrity.append_data s.log code _ (Or.inr rfl) _ hart
      | release B v t rr => exact SpinlockCodeIntegrity.append_data s.log code _ (Or.inl rfl) _ hart

theorem step_scenery [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    {program program' : SailM Unit} {observations : List Observation} {forks : List Expr}
    (control : CursorControl g cpu program c) (code : SpinlockCodeIntegrity.CodeUnwritten g.log)
    (live : ThreadLive g gen)
    (step : Step SpinlockImage.image (.hart gen cpu program) g observations
      (.hart gen cpu program') g' forks) :
    g'.devices = g.devices ∧ SpinlockCodeIntegrity.CodeUnwritten g'.log := by
  cases step with
  | hartDead _ _ _ _ dead => exact False.elim (dead live)
  | hartLive _ _ _ _ _ _ _ actual =>
    obtain ⟨after, node, rfl⟩ := actual
    exact head_node_scenery (EventPlanHead.head_of_plan control.2.2) code node

end MachCSL.Machine.SpinlockPool
