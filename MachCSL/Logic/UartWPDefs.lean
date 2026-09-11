import MachCSL.Logic.UartGhostDefs
import MachCSL.Logic.EraDevicesDefs
import MachCSL.Logic.DeadThreadDefs
import MachCSL.Logic.ObservationInvariantDefs
import MachCSL.Devices.Plic.Plan

/-! Source `WpUart.v:782–821`: separate UART and PLIC invariant custody,
and the observation permit consumed after an actual UART transition. -/
namespace MachCSL.Logic.UartWP
open Iris Iris.BI MachCSL.Machine
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]

def uartBody (capacity : MachineInterp.Capacity GF) (ghost : UartGhost.Capacity GF)
    (era : Era.Record) (names : UartGhost.Names) : IProp GF :=
  iprop(∃ u : Devices.Uart.State, Device.uartFrag capacity.era.devices era.uart u ∗
    UartGhost.ghosts ghost names u)
def plicBody (capacity : MachineInterp.Capacity GF) (era : Era.Record) : IProp GF :=
  iprop(∃ p : Devices.Plic.State, Device.plicFrag capacity.era.devices era.plic p ∗
    ⌜Devices.Plic.PlicPlanOK p⌝)
def uartInv (capacity : MachineInterp.Capacity GF) (ghost : UartGhost.Capacity GF)
    (N : Namespace) (era : Era.Record) (names : UartGhost.Names) : IProp GF :=
  inv N (uartBody capacity ghost era names)
def plicInv (capacity : MachineInterp.Capacity GF) (N : Namespace) (era : Era.Record) : IProp GF :=
  inv N (plicBody capacity era)

/-- General source permit. Its caller must supply trace custody or a ledger
protocol; no assumption about an unproved machine successor is hidden here. -/
def obsPermit (capacity : MachineInterp.Capacity GF) (ghost : UartGhost.Capacity GF)
    (N : Namespace) (γ : GName) (names : UartGhost.Names) : IProp GF :=
  iprop(□ ∀ (history events : List Observation) (d : Devices.State) (next : Devices.Uart.State),
    ⌜UartStep d events {d with uart := next}⌝ -∗
    ⌜TraceShape history true⌝ -∗ ⌜outputBytes (openSegment history) = d.uart.wire⌝ -∗
    UartGhost.ghosts ghost names next -∗ PowerGhost.obsAuth capacity.power γ history
      ={⊤ \ ↑N}=∗ UartGhost.ghosts ghost names next ∗
        PowerGhost.obsAuth capacity.power γ (history ++ events))

/-- Exact ledger hooks from `uart_obs_permit_ledger`: TX receives the wire
agreement and requires non-loopback; RX admits every environment byte. -/
def txLedgerLaw (ghost : UartGhost.Capacity GF) (Nuart Nobs : Namespace)
    (names : UartGhost.Names) (R : List Observation → IProp GF) : IProp GF :=
  iprop(□ ∀ (history : List Observation) (byte : Memory.Byte) (u next : Devices.Uart.State),
    ⌜Devices.Uart.txPop u = some (byte, next)⌝ -∗ ⌜Devices.Uart.loopback u = false⌝ -∗
    ⌜TraceShape history true⌝ -∗ ⌜outputBytes (openSegment history) = u.wire⌝ -∗
    UartGhost.ghosts ghost names next -∗ R history ={(⊤ \ ↑Nuart) \ ↑Nobs}=∗
      UartGhost.ghosts ghost names next ∗ R (history ++ [.uartOut byte]))
def rxLedgerLaw (ghost : UartGhost.Capacity GF) (Nuart Nobs : Namespace)
    (names : UartGhost.Names) (R : List Observation → IProp GF) : IProp GF :=
  iprop(□ ∀ (history : List Observation) (byte : Memory.Byte) (u next : Devices.Uart.State),
    ⌜Devices.Uart.rxPush u byte = some next⌝ -∗ ⌜TraceShape history true⌝ -∗
    UartGhost.ghosts ghost names next -∗ R history ={(⊤ \ ↑Nuart) \ ↑Nobs}=∗
      UartGhost.ghosts ghost names next ∗ R (history ++ [.uartIn byte]))

end MachCSL.Logic.UartWP
