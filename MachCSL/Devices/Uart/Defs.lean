import Std

/-!
The complete pure UART transition functions in `iris/DevModel.v:94–440`, plus
its board reset at1133, at xv6iris fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.
Byte registers use `BitVec 8`; offsets retain unbounded signed integer semantics.
The source's deliberate device abstractions and quirks are preserved.
-/
namespace MachCSL.Devices.Uart

abbrev Byte := BitVec 8

def base : Int := 0x10000000
def size : Int := 8
def irqId : Nat := 10
def fifoDepth : Nat := 16

/-- Field order agrees with source `uart_state`, with the `u_` prefix removed. -/
structure State where
  rx : List Byte
  tx : List Byte
  out : List Byte
  wire : List Byte
  ier : Byte
  lcr : Byte
  fcr : Byte
  dll : Byte
  dlm : Byte
  mcr : Byte
  scr : Byte
  rbr : Byte
  thri : Bool
  deriving DecidableEq, Repr

def dlab (u : State) : Bool := u.lcr.getLsbD 7
def fifoEnabled (u : State) : Bool := u.fcr.getLsbD 0
def loopback (u : State) : Bool := u.mcr.getLsbD 4
def rxReady (u : State) : Bool := !u.rx.isEmpty
def thre (u : State) : Bool := u.tx.isEmpty

def rxInterrupt (u : State) : Bool := u.ier.getLsbD 0 && rxReady u
def txInterrupt (u : State) : Bool := u.ier.getLsbD 1 && u.thri
def irq (u : State) : Bool := rxInterrupt u || txInterrupt u

def lsr (u : State) : Byte :=
  (if rxReady u then 1 else 0) + (if thre u then 0x60 else 0)

def isr (u : State) : Byte :=
  (if fifoEnabled u then 0xc0 else 0) +
    (if rxInterrupt u then 0x04 else if txInterrupt u then 0x02 else 0x01)

def isrThri (u : State) : Bool := !rxInterrupt u && txInterrupt u

def msrIdle : Byte := 0xb0

def msr (u : State) : Byte :=
  if loopback u then
    ((u.mcr &&& 0x0c) <<< 4) |||
      (((u.mcr &&& 0x02) <<< 3) ||| ((u.mcr &&& 0x01) <<< 5))
  else msrIdle

/-- Reading ISR may acknowledge THRI; reading RHR pops RX but retains RBR. -/
def read (u : State) (offset : Int) : Option (Byte × State) :=
  if offset = 0 then
    if dlab u then some (u.dll, u)
    else match u.rx with
      | [] => some ((if fifoEnabled u then 0 else u.rbr), u)
      | b :: rest => some (b, {u with rx := rest})
  else if offset = 1 then
    if dlab u then some (u.dlm, u) else some (u.ier, u)
  else if offset = 2 then
    some (isr u, if isrThri u then {u with thri := false} else u)
  else if offset = 3 then some (u.lcr, u)
  else if offset = 4 then some (u.mcr, u)
  else if offset = 5 then some (lsr u, u)
  else if offset = 6 then some (msr u, u)
  else if offset = 7 then some (u.scr, u)
  else none

/-- Full THR writes drop their byte but still disarm the transmit interrupt.
FCR FIFO-enable changes flush both queues; clearing TX arms the latch. -/
def write (u : State) (offset : Int) (b : Byte) : Option State :=
  if offset = 0 then
    if dlab u then some {u with dll := b}
    else if u.tx.length < fifoDepth then some {u with tx := u.tx ++ [b], thri := false}
    else some {u with thri := false}
  else if offset = 1 then
    if dlab u then some {u with dlm := b}
    else
      let ier := b &&& 0x0f
      some {u with ier := ier, thri := u.thri || (ier.getLsbD 1 && thre u)}
  else if offset = 2 then
    let flush := Bool.xor (b.getLsbD 0) (fifoEnabled u)
    let clearRx := flush || b.getLsbD 1
    let clearTx := flush || b.getLsbD 2
    some {u with rx := if clearRx then [] else u.rx,
                 tx := if clearTx then [] else u.tx,
                 fcr := b &&& 0xc9, thri := u.thri || clearTx}
  else if offset = 3 then some {u with lcr := b}
  else if offset = 4 then some {u with mcr := b &&& 0x1f}
  else if offset = 7 then some {u with scr := b}
  else if offset = 5 ∨ offset = 6 then some u
  else none

/-- Internal receive: overruns drop the queued byte but always update RBR. -/
def recv (u : State) (b : Byte) : State :=
  {u with rx := if u.rx.length < fifoDepth then u.rx ++ [b] else u.rx, rbr := b}

/-- Transmitter completion always grows out; loopback suppresses wire output
and feeds the receiver, even when that receiver overruns. -/
def txPop (u : State) : Option (Byte × State) :=
  match u.tx with
  | [] => none
  | b :: rest =>
    let next := {u with
      tx := rest
      out := u.out ++ [b]
      wire := if loopback u then u.wire else u.wire ++ [b]
      thri := (match rest with | [] => true | _ => u.thri)}
    some (b, if loopback u then recv next b else next)

/-- Host receive: a full FIFO refuses the event instead of overrunning. -/
def rxPush (u : State) (b : Byte) : Option State :=
  if u.rx.length < fifoDepth then some (recv u b) else none

def accepted (u : State) : List Byte := u.out ++ u.tx

/-- QEMU-board reset, including its nonzero divisor and OUT2 modem output. -/
def initial : State :=
  ⟨[], [], [], [], 0, 0, 0, 0x0c, 0, 0x08, 0, 0, false⟩

end MachCSL.Devices.Uart
