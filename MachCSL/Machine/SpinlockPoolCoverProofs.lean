import MachCSL.Machine.SpinlockPoolHartCoverProofs
import MachCSL.Machine.SpinlockPoolPowerOnProofs

namespace MachCSL.Machine.SpinlockPool

/-- Every actual scheduler choice, event result, blocked arm, device action
and power transition admits its deterministic annotation and preserves PoolInv. -/
theorem covers [Platform] : AnnotatedPool.Covers SpinlockImage.image Transition PoolInv := by
  intro left right e label g observations e' g' forks inv step
  have matching := inv.1.labels e label (List.mem_append_right _ (List.mem_cons_self ..))
  cases e with
  | hart gen cpu program =>
    cases label with
    | worker => contradiction
    | hart c =>
      by_cases live : ThreadLive g gen
      · exact cover_live_hart inv live step
      · exact cover_stale_hart inv live step
  | uart gen =>
    cases label with
    | hart c => contradiction
    | worker => exact cover_uart inv step
  | disk gen =>
    cases label with
    | hart c => contradiction
    | worker => exact cover_disk inv step
  | plic gen =>
    cases label with
    | hart c => contradiction
    | worker => exact cover_plic inv step
  | power =>
    cases label with
    | hart c => contradiction
    | worker =>
      have events : observations = [.powerOff] ∨ observations = [.powerOn] := by
        cases step with
        | power _ _ _ _ action => cases action <;> simp
      rcases events with rfl | rfl
      · exact cover_power_off inv step
      · exact cover_power_on inv step

/-- The complete operational annotation contract, with coverage proved from
the actual machine relation rather than supplied by a client. -/
theorem actual [Platform] : SpinlockPoolSpec :=
  ⟨initial, covers, fun _ _ _ inv left right => holder_exclusion inv left right⟩

end MachCSL.Machine.SpinlockPool
