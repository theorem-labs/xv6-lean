import MachCSL.Logic.EraStateDefs
import MachCSL.Logic.DeadThreadDefs

namespace MachCSL.Logic.RestartWP
open MachCSL.Machine

def clearReservation (g : State) (cpu : CPU) : State :=
  {g with reservations := updateHart g.reservations cpu none}

end MachCSL.Logic.RestartWP
