import Xv6.Kernel.MycpuKptWitnessResultProofs

namespace Xv6.Kernel.MycpuKptWitness
open MachCSL MachCSL.Machine MachCSL.Memory
attribute [local instance] platform

/-- The finite loop bound counts actual generated cycles, not instructions in an
independent evaluator. Its supplied equations are discharged by kernel certificates. -/
theorem cycles_from_checks
    (checked : ∀ i : Fin 14, run cachedImage cpu 4 (cycle false) (stateAt i.val) = some (stateAt (i.val+1)))
    (count start : Nat) (bound : start + count ≤ 14) :
    Cycles count (stateAt start) (stateAt (start+count)) := by
  induction count generalizing start with
  | zero => exact .nil _
  | succ count ih =>
    have step := run_sound image cachedImage cpu cached_image 4 (cycle false) (stateAt start) (stateAt (start+1))
      (Nat.zero_le _) (checked ⟨start, by omega⟩)
    have rest := ih (start+1) (by omega)
    have joined := Cycles.cons (s := stateAt start) step rest
    have equal : start + 1 + count = start + (count + 1) := by omega
    rw [equal] at joined
    exact joined

theorem operational_from_cycles (steps : Cycles 14 initial (stateAt 14)) :
    NodeSteps Devices.bus (fun _ => False) (hartAgent cpu) image
      (.pure ()) initial (.pure ()) (stateAt 14) := cycles_steps steps

theorem pool_from_operational
    (steps : NodeSteps Devices.bus (fun _ => False) (hartAgent cpu) image
      (.pure ()) initial (.pure ()) (stateAt 14)) :
    ∃ n, PoolSteps Xv6.Machine.bootImage n
      ([.hart 0 cpu (.pure ())], configured) []
      ([.hart 0 cpu (.pure ())], writeBack configured cpu (stateAt 14)) := by
  apply focused_nodeSteps_poolSteps Xv6.Machine.bootImage configured cpu 0
    (show ThreadLive configured 0 from ⟨rfl, rfl⟩) [] [] (.pure ()) (.pure ()) (stateAt 14)
  rw [configured_others, configured_focus]
  exact steps

private theorem pool_zero_eq {before after : Configuration}
    (steps : PoolSteps Xv6.Machine.bootImage 0 before [] after) : before = after := by
  cases steps
  rfl

theorem pool_positive_from_operational
    (steps : NodeSteps Devices.bus (fun _ => False) (hartAgent cpu) image
      (.pure ()) initial (.pure ()) (stateAt 14)) :
    ∃ n, 0 < n ∧ PoolSteps Xv6.Machine.bootImage n
      ([.hart 0 cpu (.pure ())], configured) []
      ([.hart 0 cpu (.pure ())], writeBack configured cpu (stateAt 14)) := by
  obtain ⟨n, run⟩ := pool_from_operational steps
  by_cases zero : n = 0
  · subst n
    have same := congrArg (fun pair : Configuration => pair.2.registers cpu .PC) (pool_zero_eq run)
    have distinct : configured.registers cpu .PC ≠
        (writeBack configured cpu (stateAt 14)).registers cpu .PC := by decide
    exact False.elim (distinct same)
  · exact ⟨n, Nat.pos_of_ne_zero zero, run⟩

theorem final_memory_ok
    (steps : NodeSteps Devices.bus (fun _ => False) (hartAgent cpu) image
      (.pure ()) initial (.pure ()) (stateAt 14)) :
    MemoryOK finalState ∧ ReservationsOK finalState := by
  obtain ⟨n, run⟩ := pool_from_operational steps
  exact ⟨reachable_memory_ok Xv6.Machine.bootImage n _ _ [] configured_memory_ok run,
    reachable_reservations_ok Xv6.Machine.bootImage n _ _ [] configured_reservations_ok run⟩

/-- Lift the actual selected-hart derivation without dropping any workers. -/
theorem full_pool_from_operational
    (steps : NodeSteps Devices.bus (fun _ => False) (hartAgent cpu) image
      (.pure ()) initial (.pure ()) (stateAt 14)) :
    ∃ n, 0 < n ∧ PoolSteps Xv6.Machine.bootImage n
      (.power :: powerFork 0, configured) [] (.power :: powerFork 0, finalState) := by
  have focused : NodeSteps Devices.bus (othersReserved configured.reservations cpu)
      (hartAgent cpu) configured.image (.pure ()) (focus configured cpu)
      (.pure ()) (stateAt 14) := by
    rw [configured_others, configured_focus]
    exact steps
  obtain ⟨n, run⟩ := focused_nodeSteps_poolSteps Xv6.Machine.bootImage configured cpu 0
    (show ThreadLive configured 0 from ⟨rfl, rfl⟩)
    [.power, loop 0 0, loop 0 1, loop 0 2]
    [loop 0 4, loop 0 5, loop 0 6, loop 0 7, .uart 0, .disk 0, .plic 0]
    (.pure ()) (.pure ()) (stateAt 14) focused
  by_cases zero : n = 0
  · subst n
    have same := congrArg (fun pair : Configuration => pair.2.registers cpu .PC) (pool_zero_eq run)
    have distinct : configured.registers cpu .PC ≠ finalState.registers cpu .PC := by decide
    exact False.elim (distinct same)
  · exact ⟨n, Nat.pos_of_ne_zero zero, run⟩

theorem full_pool_length : (.power :: powerFork 0).length = 12 := by
  rw [List.length_cons, powerFork_length]

end Xv6.Kernel.MycpuKptWitness
