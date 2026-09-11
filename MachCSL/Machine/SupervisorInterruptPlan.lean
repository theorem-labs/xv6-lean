import MachCSL.Machine.SupervisorInterruptProofs

namespace MachCSL.Machine.SupervisorInterrupt
open MachCSL.Logic.EventWP LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

theorem currentlyEnabled_s_plan (reads : ReadAllowed) (rs : RegisterFile)
    (enabled : _get_Misa_S (rs .misa) = 1#1) :
    Returns reads rs (currentlyEnabled .Ext_S) true rs := by
  unfold currentlyEnabled
  refine (read_plan reads rs .misa (by decide)).bind ?_
  rw [enabled, show currentlyEnabled .Ext_Zicsr = pure true by
    unfold currentlyEnabled
    rw [show hartSupports .Ext_Zicsr = true by unfold hartSupports; rfl]]
  rw [show hartSupports .Ext_S = true by unfold hartSupports; rfl]
  exact pure_plan reads rs true

/-- Both pin results are independent universal branches of the event plan. -/
theorem external_plan (reads : ReadAllowed) (rs : RegisterFile)
    (enabled : _get_Misa_S (rs .misa) = 1#1) :
    ExecPlan reads rs (external_interrupts_pending ())
      (fun value after => (∃ meip seip, value = externalValue meip seip) ∧ after = rs) := by
  unfold external_interrupts_pending
  apply ExecPlan.readPin (by decide)
  intro meip
  dsimp only [_root_.Sail.ArchSem.FreeM.bind]
  refine ExecPlan.bind (currentlyEnabled_s_plan reads rs enabled) ?_
  intro value after same
  rcases same with ⟨valueEq, afterEq⟩
  subst after
  subst value
  apply ExecPlan.readPin (by decide)
  intro seip
  exact .pure ⟨⟨meip, seip, rfl⟩, rfl⟩

theorem read_mip_plan (reads : ReadAllowed) (rs : RegisterFile)
    (enabled : _get_Misa_S (rs .misa) = 1#1) :
    ExecPlan reads rs (read_mip .IncludePlatformInterrupts)
      (fun value after => (∃ meip seip, value = pendingValue rs meip seip) ∧ after = rs) := by
  unfold read_mip
  refine ExecPlan.bind (read_plan reads rs .mip (by decide)) ?_
  intro value after same
  rcases same with ⟨valueEq, afterEq⟩
  subst after
  subst value
  refine ExecPlan.bind (external_plan reads rs enabled) ?_
  intro value after same
  rcases same with ⟨⟨meip, seip, valueEq⟩, afterEq⟩
  subst after
  subst value
  exact .pure ⟨⟨meip, seip, rfl⟩, rfl⟩

theorem getPendingSet_plan (reads : ReadAllowed) (rs : RegisterFile)
    (disabled : Disabled rs) :
    Returns reads rs (getPendingSet .Supervisor) none rs := by
  unfold getPendingSet
  refine (currentlyEnabled_s_plan reads rs disabled.supervisorEnabled).bind ?_
  refine (read_plan reads rs .mideleg (by decide)).bind ?_
  refine ExecPlan.bind (read_mip_plan reads rs disabled.supervisorEnabled) ?_
  intro pending after same
  have afterEq := same.2
  subst after
  refine (read_plan reads rs .mie (by decide)).bind ?_
  refine (read_plan reads rs .mie (by decide)).bind ?_
  refine (read_plan reads rs .mstatus (by decide)).bind ?_
  refine (read_plan reads rs .mstatus (by decide)).bind ?_
  rw [machine_pending_zero rs disabled pending, disabled.sie]
  exact pure_plan reads rs none

theorem dispatch_plan (reads : ReadAllowed) (rs : RegisterFile)
    (disabled : Disabled rs) :
    Returns reads rs (dispatchInterrupt .Supervisor) none rs := by
  unfold dispatchInterrupt
  exact (getPendingSet_plan reads rs disabled).bind (pure_plan reads rs none)

end MachCSL.Machine.SupervisorInterrupt
