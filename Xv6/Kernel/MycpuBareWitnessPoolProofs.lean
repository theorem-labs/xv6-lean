import Xv6.Kernel.MycpuBareWitnessProofs
import MachCSL.Logic.SupervisorBitsDefs

namespace Xv6.Kernel.MycpuBareWitness
open MachCSL MachCSL.Machine MachCSL.Memory
attribute [local instance] platform

/-- The power worker, all eight harts and all three device workers are
present. The existing focused construction schedules only CPU three. -/
theorem full_pool : ∃ n, PoolSteps Xv6.Machine.bootImage n
    (.power :: powerFork 0, configured) []
    (.power :: powerFork 0, writeBack configured cpu (stateAt 14)) := by
  have steps : NodeSteps Devices.bus (othersReserved configured.reservations cpu)
      (hartAgent cpu) configured.image (.pure ()) (focus configured cpu)
      (.pure ()) (stateAt 14) := by
    rw [configured_others, configured_focus]
    exact operational
  have run := focused_nodeSteps_poolSteps Xv6.Machine.bootImage configured cpu 0
    (show ThreadLive configured 0 from ⟨rfl, rfl⟩)
    [.power, loop 0 0, loop 0 1, loop 0 2]
    [loop 0 4, loop 0 5, loop 0 6, loop 0 7, .uart 0, .disk 0, .plic 0]
    (.pure ()) (.pure ()) (stateAt 14) steps
  exact run

private theorem full_pool_zero_eq {before after : Configuration}
    (steps : PoolSteps Xv6.Machine.bootImage 0 before [] after) : before = after := by
  cases steps
  rfl

/-- Positive execution in the actual twelve-thread pool, with the same
configured state and final record as the original fourteen-cycle witness. -/
theorem full_pool_positive : ∃ n, 0 < n ∧ PoolSteps Xv6.Machine.bootImage n
    (.power :: powerFork 0, configured) []
    (.power :: powerFork 0, writeBack configured cpu (stateAt 14)) := by
  obtain ⟨n, run⟩ := full_pool
  by_cases zero : n = 0
  · subst n
    have same : configured = writeBack configured cpu (stateAt 14) :=
      congrArg Prod.snd (full_pool_zero_eq run)
    have pc := congrArg (fun g : State => g.registers cpu .PC) same
    have distinct : configured.registers cpu .PC ≠
        (writeBack configured cpu (stateAt 14)).registers cpu .PC := by decide
    exact False.elim (distinct pc)
  · exact ⟨n, Nat.pos_of_ne_zero zero, run⟩

theorem full_pool_length : (.power :: powerFork 0).length = 12 := by
  rw [List.length_cons, powerFork_length]

/-- All ten source supervisor mstatus facts hold of the concrete entry.
This is a pure fact, not allocation of the corresponding Iris resources. -/
theorem entry_ms_facts : Logic.SupervisorBits.MsFacts (entry .mstatus) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Xv6.Kernel.MycpuBareWitness
