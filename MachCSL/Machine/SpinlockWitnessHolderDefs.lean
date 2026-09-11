import MachCSL.Machine.SpinlockWitnessReleasePoolProofs
import MachCSL.Machine.SpinlockPoolReachability

namespace MachCSL.Machine.SpinlockWitnessHolder
open MachCSL.Memory MachCSL.Machine.SpinlockWitness MachCSL.Machine.SpinlockWitnessHeld

/-- CPU0 has retired ADDIW and the non-taken retry branch after its successful
AMO. Its actual PC is now at the counter-load body instruction. -/
def boundaryLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (workAfter 2) memoryOne logOne 1 none devices

def state (before : State) : State :=
  writeBack (swapped before) 0 (boundaryLocal (Devices.reset before.devices))

def pool (generation : Nat) : List Expr :=
  pairPool generation (.pure ()) (paused 1).1

end MachCSL.Machine.SpinlockWitnessHolder
