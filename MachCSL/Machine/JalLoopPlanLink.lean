import MachCSL.Machine.JalLoopPlanCycle
import MachCSL.Machine.JalLoopPlanFetch

/-! Concrete fetched-cycle plans and closure of their explicit snapshot premise.
The PMP snapshot premise still concerns the concrete reset witness; it is not
silently generalized to every power-on permitted by BootFacts. -/
namespace MachCSL.Machine.JalLoopPlan
open MachCSL.Logic.EventWP

abbrev SnapshotCovered (cpu : CPU) (rs : RegisterFile) :=
  JalLoop.Covers (JalLoop.fetchSnapshot (BitVec.ofNat 64 cpu.val)) rs

theorem snapshot_enable (cpu : CPU) (rs : RegisterFile) (covered : SnapshotCovered cpu rs) :
    SnapshotCovered cpu (enableAfter rs) :=
  covers_write _ rs covered .minstret_increment _ rfl

theorem snapshot_retire (cpu : CPU) (rs : RegisterFile) (covered : SnapshotCovered cpu rs) :
    SnapshotCovered cpu (retireAfter rs) := by
  unfold retireAfter
  split
  · exact covers_write _ _ (snapshot_enable cpu rs covered) .minstret _ rfl
  · exact snapshot_enable cpu rs covered

theorem snapshot_clock (cpu : CPU) (rs : RegisterFile) (covered : SnapshotCovered cpu rs) :
    SnapshotCovered cpu (clockAfter rs) := by
  unfold clockAfter timeAfter counterAfter JalLoop.clintAfter
  split
  · exact covers_write _ _ (covers_write _ _
      (covers_write _ _ covered .mcycle _ rfl) .mtime _ rfl) .mip _ rfl
  · exact covers_write _ _ (covers_write _ _ covered .mtime _ rfl) .mip _ rfl

theorem snapshot_cycle (cpu : CPU) (tick : Bool) (rs : RegisterFile)
    (covered : SnapshotCovered cpu rs) : SnapshotCovered cpu (cycleAfter tick rs) := by
  cases tick
  · exact snapshot_retire cpu rs covered
  · exact snapshot_clock cpu _ (snapshot_retire cpu rs covered)

theorem fetched_cycle_plan [Platform] (cpu : CPU) (tick : Bool) (rs : RegisterFile)
    (static : Static rs) (covered : SnapshotCovered cpu rs) :
    Returns CodeRead rs (cycle tick) () (cycleAfter tick rs) :=
  cycle_plan CodeRead rs static tick (fetch_plan cpu _ (snapshot_enable cpu rs covered))

end MachCSL.Machine.JalLoopPlan
