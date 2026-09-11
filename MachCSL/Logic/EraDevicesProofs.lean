import MachCSL.Logic.EraDevicesSpec

namespace MachCSL.Logic.EraDevices
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Era.Capacity GF)

theorem devices_access (era : Era.Record) (g : State) :
    iprop(⊢ Era.interp capacity era g -∗ Device.interp capacity.devices era.deviceNames g.devices ∗
      (∀ devices, ⌜devices.virtio.v_disk = g.devices.virtio.v_disk⌝ -∗
        Device.interp capacity.devices era.deviceNames devices -∗
        Era.interp capacity era (withDevices g devices))) := by
  unfold Era.interp
  iintro ⟨Hr, Hh, Hd, Hrest⟩
  isplitl [Hd]
  · iexact Hd
  · iintro %devices %disk Hd
    have heap : Era.heapInterpAt capacity era (withDevices g devices) = Era.heapInterpAt capacity era g := rfl
    have tso : Tso.Interp.tsoInterpAt capacity.tso era.tsoNames era.imageBytes (withDevices g devices) =
      Tso.Interp.tsoInterpAt capacity.tso era.tsoNames era.imageBytes g := rfl
    have resv : ReservationsOK (withDevices g devices) = ReservationsOK g := rfl
    rw [heap, tso, resv]
    unfold withDevices
    rw [disk]
    iframe

theorem read_uart (contracts : Device.DeviceSpec capacity.devices) (era : Era.Record) (g : State)
    (uart : MachCSL.Devices.Uart.State) :
    iprop(⊢ Era.interp capacity era g -∗ Device.uartFrag capacity.devices era.uart uart -∗
      ⌜g.devices.uart = uart⌝) := by
  unfold Era.interp Device.interp
  iintro ⟨_, _, ⟨Hu, _, _⟩, _⟩ Hvalue
  iunfold Era.Record.deviceNames at Hu
  ihave %eq := contracts.uart_agree era.uart g.devices.uart uart $$ Hu Hvalue
  ipureintro
  exact eq.symm

theorem read_plic (contracts : Device.DeviceSpec capacity.devices) (era : Era.Record) (g : State)
    (plic : MachCSL.Devices.Plic.State) :
    iprop(⊢ Era.interp capacity era g -∗ Device.plicFrag capacity.devices era.plic plic -∗
      ⌜g.devices.plic = plic⌝) := by
  unfold Era.interp Device.interp
  iintro ⟨_, _, ⟨_, Hp, _⟩, _⟩ Hvalue
  iunfold Era.Record.deviceNames at Hp
  ihave %eq := contracts.plic_agree era.plic g.devices.plic plic $$ Hp Hvalue
  ipureintro
  exact eq.symm

theorem write_uart (contracts : Device.DeviceSpec capacity.devices) (era : Era.Record) (g : State)
    (old uart : MachCSL.Devices.Uart.State) :
    iprop(⊢ Era.interp capacity era g -∗ Device.uartFrag capacity.devices era.uart old ==∗
      Era.interp capacity era (withUart g uart) ∗ Device.uartFrag capacity.devices era.uart uart) := by
  iintro Hera Hvalue
  ihave ⟨Hd, Hback⟩ := devices_access capacity era g $$ Hera
  iunfold Device.interp at Hd
  icases Hd with ⟨Hu, Hp, Hv⟩
  iunfold Era.Record.deviceNames at Hu
  imod contracts.uart_update era.uart g.devices.uart old uart $$ Hu Hvalue with ⟨Hu, Hvalue⟩
  imodintro
  iframe Hvalue
  unfold withUart
  iapply Hback
  · ipureintro; rfl
  · unfold Device.interp Era.Record.deviceNames
    iframe

theorem write_plic (contracts : Device.DeviceSpec capacity.devices) (era : Era.Record) (g : State)
    (old plic : MachCSL.Devices.Plic.State) :
    iprop(⊢ Era.interp capacity era g -∗ Device.plicFrag capacity.devices era.plic old ==∗
      Era.interp capacity era (withPlic g plic) ∗ Device.plicFrag capacity.devices era.plic plic) := by
  iintro Hera Hvalue
  ihave ⟨Hd, Hback⟩ := devices_access capacity era g $$ Hera
  iunfold Device.interp at Hd
  icases Hd with ⟨Hu, Hp, Hv⟩
  iunfold Era.Record.deviceNames at Hp
  imod contracts.plic_update era.plic g.devices.plic old plic $$ Hp Hvalue with ⟨Hp, Hvalue⟩
  imodintro
  iframe Hvalue
  unfold withPlic
  iapply Hback
  · ipureintro; rfl
  · unfold Device.interp Era.Record.deviceNames
    iframe

theorem eraDevicesSpec : EraDevicesSpec capacity :=
  ⟨devices_access capacity, read_uart capacity, read_plic capacity, write_uart capacity, write_plic capacity⟩

end MachCSL.Logic.EraDevices
