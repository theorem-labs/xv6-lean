import MachCSL.Logic.EraDevicesDefs

namespace MachCSL.Logic.EraDevices
open Iris Iris.BI MachCSL.Machine

structure EraDevicesSpec {GF : BundledGFunctors} (capacity : Era.Capacity GF) : Prop where
  access : ∀ era g,
    iprop(⊢ Era.interp capacity era g -∗ Device.interp capacity.devices era.deviceNames g.devices ∗
      (∀ devices, ⌜devices.virtio.v_disk = g.devices.virtio.v_disk⌝ -∗
        Device.interp capacity.devices era.deviceNames devices -∗
        Era.interp capacity era (withDevices g devices)))
  uartRead : Device.DeviceSpec capacity.devices → ∀ era g uart,
    iprop(⊢ Era.interp capacity era g -∗ Device.uartFrag capacity.devices era.uart uart -∗
      ⌜g.devices.uart = uart⌝)
  plicRead : Device.DeviceSpec capacity.devices → ∀ era g plic,
    iprop(⊢ Era.interp capacity era g -∗ Device.plicFrag capacity.devices era.plic plic -∗
      ⌜g.devices.plic = plic⌝)
  uartWrite : Device.DeviceSpec capacity.devices → ∀ era g old uart,
    iprop(⊢ Era.interp capacity era g -∗ Device.uartFrag capacity.devices era.uart old ==∗
      Era.interp capacity era (withUart g uart) ∗ Device.uartFrag capacity.devices era.uart uart)
  plicWrite : Device.DeviceSpec capacity.devices → ∀ era g old plic,
    iprop(⊢ Era.interp capacity era g -∗ Device.plicFrag capacity.devices era.plic old ==∗
      Era.interp capacity era (withPlic g plic) ∗ Device.plicFrag capacity.devices era.plic plic)

end MachCSL.Logic.EraDevices
