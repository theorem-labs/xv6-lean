import MachCSL.Logic.EraDevicesProofs
import MachCSL.Logic.EraStateLink

namespace MachCSL.Logic.EraDevices

theorem registryEraDevicesSpec : EraDevicesSpec Era.capacity := eraDevicesSpec Era.capacity

end MachCSL.Logic.EraDevices

namespace MachCSL.Logic.MachineInterp
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem power_read_uart (names : FixedNames) (g : State) (generation : Nat) (era : Era.Record)
    (live : ThreadLive g generation) (uart : MachCSL.Devices.Uart.State) :
    iprop(⊢ powerInterp capacity names g -∗ generationCertificate capacity names generation era -∗
      Device.uartFrag capacity.era.devices era.uart uart -∗ ⌜g.devices.uart = uart⌝) := by
  iintro Hp Hcert Hvalue
  ihave ⟨Hera, _⟩ := live_era_access capacity names g generation era live $$ Hp Hcert
  iapply EraDevices.read_uart capacity.era (Device.deviceSpec _) era g uart $$ Hera Hvalue

theorem power_read_plic (names : FixedNames) (g : State) (generation : Nat) (era : Era.Record)
    (live : ThreadLive g generation) (plic : MachCSL.Devices.Plic.State) :
    iprop(⊢ powerInterp capacity names g -∗ generationCertificate capacity names generation era -∗
      Device.plicFrag capacity.era.devices era.plic plic -∗ ⌜g.devices.plic = plic⌝) := by
  iintro Hp Hcert Hvalue
  ihave ⟨Hera, _⟩ := live_era_access capacity names g generation era live $$ Hp Hcert
  iapply EraDevices.read_plic capacity.era (Device.deviceSpec _) era g plic $$ Hera Hvalue

theorem power_write_uart (names : FixedNames) (g : State) (generation : Nat) (era : Era.Record)
    (live : ThreadLive g generation) (old uart : MachCSL.Devices.Uart.State) :
    iprop(⊢ powerInterp capacity names g -∗ generationCertificate capacity names generation era -∗
      Device.uartFrag capacity.era.devices era.uart old ==∗
      powerInterp capacity names (EraDevices.withUart g uart) ∗ Device.uartFrag capacity.era.devices era.uart uart) :=
  live_update capacity names g (EraDevices.withUart g uart) generation era live rfl rfl rfl _ _
    (EraDevices.write_uart capacity.era (Device.deviceSpec _) era g old uart)

theorem power_write_plic (names : FixedNames) (g : State) (generation : Nat) (era : Era.Record)
    (live : ThreadLive g generation) (old plic : MachCSL.Devices.Plic.State) :
    iprop(⊢ powerInterp capacity names g -∗ generationCertificate capacity names generation era -∗
      Device.plicFrag capacity.era.devices era.plic old ==∗
      powerInterp capacity names (EraDevices.withPlic g plic) ∗ Device.plicFrag capacity.era.devices era.plic plic) :=
  live_update capacity names g (EraDevices.withPlic g plic) generation era live rfl rfl rfl _ _
    (EraDevices.write_plic capacity.era (Device.deviceSpec _) era g old plic)

end MachCSL.Logic.MachineInterp
