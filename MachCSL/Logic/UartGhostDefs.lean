import MachCSL.Logic.InvariantDefs
import MachCSL.Devices.Uart.Proofs
import Iris.BI.Lib.MonoList
import Iris.Algebra.Lib.DFracAgree

/-! Exact three-capacity/four-name UART ghost algebra from `Xv6Cameras.v`
and `WpUart.v`. Accepted and transmitted traces share one MonoList capacity. -/
namespace MachCSL.Logic.UartGhost
open Iris Iris.BI MachCSL.Memory

abbrev ListRF := constOF (MonoList (DiscreteO Byte))
abbrev DlabRF := constOF (DFracAgree.DFracAgreeR (DiscreteO Bool))
structure Capacity (GF : BundledGFunctors) where
  traces : MonoListG GF Byte
  transmitter : GhostVarG GF (List Byte)
  dlab : ElemG GF DlabRF

structure Names where
  accepted : GName
  output : GName
  transmitter : GName
  dlab : GName

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def sentAuth (names : Names) (u : Devices.Uart.State) : IProp GF :=
  letI := capacity.traces
  MonoList.auth_own names.accepted (.own 1) (Devices.Uart.accepted u)
def sent (names : Names) (bytes : List Byte) : IProp GF :=
  letI := capacity.traces
  MonoList.lb_own names.accepted bytes
def outAuth (names : Names) (u : Devices.Uart.State) : IProp GF :=
  letI := capacity.traces
  MonoList.auth_own names.output (.own 1) u.out
def outLB (names : Names) (bytes : List Byte) : IProp GF :=
  letI := capacity.traces
  MonoList.lb_own names.output bytes
def txOwn (names : Names) (bytes : List Byte) : IProp GF :=
  letI := capacity.transmitter
  ghost_var names.transmitter (.own (1 : Qp).half) bytes
def txAuth (names : Names) (u : Devices.Uart.State) : IProp GF :=
  txOwn capacity names (Devices.Uart.accepted u)
def dlabIs (names : Names) (dq : DFrac) (value : Bool) : IProp GF :=
  iOwn (E := capacity.dlab) names.dlab (DFracAgree.mk dq (DiscreteO.mk value))
def dlabAuth (names : Names) (u : Devices.Uart.State) : IProp GF :=
  dlabIs capacity names (.own (1 : Qp).half) (Devices.Uart.dlab u)
def dlabOff (names : Names) : IProp GF := dlabIs capacity names .discard false

def ghosts (names : Names) (u : Devices.Uart.State) : IProp GF :=
  iprop(sentAuth capacity names u ∗ outAuth capacity names u ∗
    txAuth capacity names u ∗ dlabAuth capacity names u)

def initialClients (names : Names) (u : Devices.Uart.State) : IProp GF :=
  iprop(txOwn capacity names (Devices.Uart.accepted u) ∗ sent capacity names (Devices.Uart.accepted u) ∗
    dlabIs capacity names (.own (1 : Qp).half) (Devices.Uart.dlab u))

end MachCSL.Logic.UartGhost
