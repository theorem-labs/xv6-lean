import Xv6.Kernel.MycpuCycleBodyDefs
import Xv6.Kernel.MycpuActiveDefs

/-! Actual setup and successful retirement/clock/restart interfaces. The active
instruction WP is a separate composition boundary, not an assumed function. -/
namespace Xv6.Kernel.MycpuCycleShell
open Iris MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev Shares := MycpuCycleBody.Shares
abbrev footprint := MycpuCycleBody.footprint
abbrev cells := @MycpuCycleBody.cells

def finish [Platform] (tick : Bool) (step : _root_.Step) : SailM Unit := do
  let _ ← SupervisorRetirement.postlude step
  if tick then tick_clock () else pure ()

def started (rs : RegisterFile) : RegisterFile :=
  SupervisorRetirement.setupAfter rs (rs .cur_privilege)

def completed (rs after : RegisterFile) : Prop :=
  SupervisorClock.OffClock (SupervisorRetirement.completeAfter rs) after

end Xv6.Kernel.MycpuCycleShell
