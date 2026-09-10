import MachCSL.Machine.State
import MachCSL.Devices.Uart.Proofs

/-! UART and interrupt-wire actors from `iris/RiscvLang.v:uart_step,plic_step`.
The explicit UART idle constructor is the source's device-totality stutter.
There is no corresponding unrestricted stutter in the hart's node relation. -/
namespace MachCSL.Machine

inductive Observation where
  | uartIn (byte : Memory.Byte)
  | uartOut (byte : Memory.Byte)
  | powerOn
  | powerOff
  deriving DecidableEq, Repr

def outputBytes : List Observation → List Memory.Byte
  | [] => []
  | .uartOut b :: rest => b :: outputBytes rest
  | _ :: rest => outputBytes rest

inductive UartStep (d : Devices.State) : List Observation → Devices.State → Prop where
  | tx (byte : Memory.Byte) (next : Devices.Uart.State)
      (pop : Devices.Uart.txPop d.uart = some (byte, next)) :
      UartStep d (if Devices.Uart.loopback d.uart then [] else [.uartOut byte])
        { d with uart := next }
  | rx (byte : Memory.Byte) (next : Devices.Uart.State)
      (push : Devices.Uart.rxPush d.uart byte = some next) :
      UartStep d [.uartIn byte] { d with uart := next }
  | latch (next : Devices.Plic.State)
      (level : Devices.irqLevel d Devices.Plic.uartIrqId = true)
      (latched : Devices.Plic.latch d.plic Devices.Plic.uartIrqId = some next) :
      UartStep d [] { d with plic := next }
  | idle : UartStep d [] d

def boolBit (b : Bool) : BitVec 1 := if b then 1 else 0

inductive PlicStep (d : Devices.State) (registers : CPU → RegisterFile) :
    (CPU → RegisterFile) → Prop where
  | supervisor (cpu : CPU) :
      PlicStep d registers (updateHart registers cpu
        (Sail.Registers.write (registers cpu) .sig_seip (boolBit (Devices.seip d cpu.val))))
  | machine (cpu : CPU) :
      PlicStep d registers (updateHart registers cpu
        (Sail.Registers.write (registers cpu) .sig_meip (boolBit (Devices.meip d cpu.val))))

theorem uart_disk (d d' : Devices.State) (observations : List Observation)
    (step : UartStep d observations d') : d'.virtio.v_disk = d.virtio.v_disk := by
  cases step <;> rfl

/-- Observable output grows exactly with bytes reaching SOUT, excluding loopback. -/
theorem uart_wire (d d' : Devices.State) (observations : List Observation)
    (step : UartStep d observations d') :
    d'.uart.wire = d.uart.wire ++ outputBytes observations := by
  cases step with
  | tx byte next pop =>
    have h := Devices.Uart.txPop_wire d.uart byte next pop
    cases hl : Devices.Uart.loopback d.uart <;> simpa [hl, outputBytes] using h
  | rx byte next push => simpa [outputBytes] using Devices.Uart.rxPush_wire _ _ _ push
  | latch next level latched => simp [outputBytes]
  | idle => simp [outputBytes]

theorem outputBytes_append (left right : List Observation) :
    outputBytes (left ++ right) = outputBytes left ++ outputBytes right := by
  induction left with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [outputBytes, ih]

end MachCSL.Machine
