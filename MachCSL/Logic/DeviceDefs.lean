import MachCSL.Devices.Fabric
import Iris.Instances.Lib.GhostVar

/-! Device halves from `RiscvPtsto.v:1914–1968` at the paper pin. -/
namespace MachCSL.Logic.Device
open Iris Iris.BI MachCSL.Devices

/-- Resource capacity is separate from the runtime names chosen at allocation. -/
structure Capacity (GF : BundledGFunctors) where
  uart : GhostVarG GF Uart.State
  plic : GhostVarG GF Plic.State
  virtio : GhostVarG GF Virtio.State

structure Names where
  uart : GName
  plic : GName
  virtio : GName

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def uartAuth (γ : GName) (u : Uart.State) : IProp GF :=
  letI := capacity.uart
  ghost_var γ (.own (1 : Qp).half) u
def uartFrag (γ : GName) (u : Uart.State) : IProp GF := uartAuth capacity γ u
def plicAuth (γ : GName) (p : Plic.State) : IProp GF :=
  letI := capacity.plic
  ghost_var γ (.own (1 : Qp).half) p
def plicFrag (γ : GName) (p : Plic.State) : IProp GF := plicAuth capacity γ p
def virtioAuth (γ : GName) (v : Virtio.State) : IProp GF :=
  letI := capacity.virtio
  ghost_var γ (.own (1 : Qp).half) v
def virtioFrag (γ : GName) (v : Virtio.State) : IProp GF := virtioAuth capacity γ v

def interp (names : Names) (d : State) : IProp GF :=
  iprop(uartAuth capacity names.uart d.uart ∗ plicAuth capacity names.plic d.plic ∗
    virtioAuth capacity names.virtio d.virtio)

/-- Client halves; allocation returns these separately from the interpretation. -/
def fragments (names : Names) (d : State) : IProp GF :=
  iprop(uartFrag capacity names.uart d.uart ∗ plicFrag capacity names.plic d.plic ∗
    virtioFrag capacity names.virtio d.virtio)

end MachCSL.Logic.Device
