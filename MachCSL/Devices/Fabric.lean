import MachCSL.Devices.Uart.Defs
import MachCSL.Devices.Plic.Defs
import MachCSL.Devices.Virtio.Defs
import MachCSL.Machine.Node

/-! Concrete MMIO fabric, `iris/DevModel.v:950–1140` at the paper pin.
Wide UART accesses address one byte register; narrow Virtio accesses return
zero or drop the write. Unsupported widths and undecoded offsets stay stuck. -/
namespace MachCSL.Devices

structure State where
  uart : Uart.State
  plic : Plic.State
  virtio : Virtio.State

def inWindow (base size address : Int) : Bool := base ≤ address && address < base + size

def read (d : State) (pa : Memory.PhysicalAddress) (n : Nat) :
    Option (BitVec (8 * n) × State) :=
  let a : Int := pa.toNat
  if inWindow Uart.base Uart.size a then
    if n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 then do
      let (byte, uart) ← Uart.read d.uart (a - Uart.base)
      pure (BitVec.ofNat (8 * n) byte.toNat, { d with uart := uart })
    else none
  else if inWindow Plic.base Plic.size a then
    if n = 4 then do
      let (word, plic) ← Plic.read d.plic (a - Plic.base)
      pure (BitVec.ofNat (8 * n) word.toNat, { d with plic := plic })
    else none
  else if inWindow Virtio.virtio_base Virtio.virtio_size a then
    if n = 4 then do
      let word ← Virtio.virtio_read d.virtio (a - Virtio.virtio_base)
      pure (BitVec.ofNat (8 * n) word.toNat, d)
    else if n = 1 ∨ n = 2 then some (0, d)
    else none
  else none

def write (d : State) (pa : Memory.PhysicalAddress) (n : Nat) (value : BitVec (8 * n)) :
    Option State :=
  let a : Int := pa.toNat
  if inWindow Uart.base Uart.size a then
    if n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 then do
      let uart ← Uart.write d.uart (a - Uart.base) (BitVec.ofNat 8 value.toNat)
      pure { d with uart := uart }
    else none
  else if inWindow Plic.base Plic.size a then
    if n = 4 then do
      let plic ← Plic.write d.plic (a - Plic.base) (BitVec.ofNat 32 value.toNat)
      pure { d with plic := plic }
    else none
  else if inWindow Virtio.virtio_base Virtio.virtio_size a then
    if n = 4 then do
      let virtio ← Virtio.virtio_write d.virtio (a - Virtio.virtio_base)
        (BitVec.ofNat 32 value.toNat)
      pure { d with virtio := virtio }
    else if n = 1 ∨ n = 2 then some d
    else none
  else none

def irqLevel (d : State) (source : Nat) : Bool :=
  if source = Plic.uartIrqId then Uart.irq d.uart
  else if source = Plic.virtioIrqId then Virtio.virtio_irq d.virtio
  else false

def seip (d : State) (hart : Nat) : Bool := Plic.eip d.plic (Plic.sCtx hart)
def meip (d : State) (hart : Nat) : Bool := Plic.eip d.plic (Plic.mCtx hart)

def initial : State := ⟨Uart.initial, Plic.initial, Virtio.virtio0_state⟩

/-- Reboot resets device control state while preserving the current disk. -/
def reset (d : State) : State :=
  ⟨Uart.initial, Plic.initial, Virtio.virtio_reset d.virtio⟩

def bus : Machine.Bus State := ⟨read, write⟩

theorem reset_disk (d : State) : (reset d).virtio.v_disk = d.virtio.v_disk := rfl

end MachCSL.Devices
