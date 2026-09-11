import MachCSL.Machine.SpinlockWitnessReleaseDefs

namespace MachCSL.Machine.SpinlockWitnessRelease
open MachCSL.Memory MachCSL.Machine.SpinlockWitness MachCSL.Machine.SpinlockWitnessHeld

def failedLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (pausedRegisters 1) memoryThree logThree 3 (none) devices

def firstReleaseLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (unlockRegisters) memoryThree logThree 1 (none) devices

def releasedLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (unlockRegisters) memoryFour logFour 1 (none) devices

def retryStartLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (pausedRegisters 1) memoryFour logFour 3 (none) devices

def retryLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (retryRegisters) memoryFour logFour 3 (none) devices

def retryReadLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (retryRegisters) memoryFour logFour 4 (some zeroSnapshot) devices

def wonLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (retryRegisters) memoryFive logFive 5 (none) devices

def incrementLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (incrementRegisters) memoryFive logFive 5 (none) devices

def incrementedLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (incrementRegisters) memorySix logSix 5 (none) devices

def releaseLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (releaseRegisters) memorySix logSix 5 (none) devices

def finalLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (releaseRegisters) memorySeven logSeven 5 (none) devices

def failedState (before : State) : State :=
  writeBack (unlockReady before) 1 (failedLocal (Devices.reset before.devices))

def releasedState (before : State) : State :=
  writeBack (failedState before) 0 (releasedLocal (Devices.reset before.devices))

def retryState (before : State) : State :=
  writeBack (releasedState before) 1 (retryLocal (Devices.reset before.devices))

def retryReadState (before : State) : State :=
  writeBack (retryState before) 1 (retryReadLocal (Devices.reset before.devices))

def wonState (before : State) : State :=
  writeBack (retryReadState before) 1 (wonLocal (Devices.reset before.devices))

def incrementState (before : State) : State :=
  writeBack (wonState before) 1 (incrementLocal (Devices.reset before.devices))

def incrementedState (before : State) : State :=
  writeBack (incrementState before) 1 (incrementedLocal (Devices.reset before.devices))

def releaseState (before : State) : State :=
  writeBack (incrementedState before) 1 (releaseLocal (Devices.reset before.devices))

def finalState (before : State) : State :=
  writeBack (releaseState before) 1 (finalLocal (Devices.reset before.devices))

def finalPool (generation : Nat) : List Expr :=
  pairPool generation (unlockResume (.Ok none)) (releaseResume (.Ok none))

end MachCSL.Machine.SpinlockWitnessRelease
