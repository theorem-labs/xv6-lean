import MachCSL.Logic.EraDefs
import MachCSL.Logic.DeviceSpec

namespace MachCSL.Logic.EraDevices
open MachCSL.Machine

def withDevices (g : State) (devices : MachCSL.Devices.State) : State :=
  { g with devices := devices }

def withUart (g : State) (uart : MachCSL.Devices.Uart.State) : State :=
  withDevices g { g.devices with uart := uart }

def withPlic (g : State) (plic : MachCSL.Devices.Plic.State) : State :=
  withDevices g { g.devices with plic := plic }

end MachCSL.Logic.EraDevices
