import MachCSL.Machine.Image
import MachCSL.Memory.ReadBytes

/-! The concrete two-hart integration image. Its raw instruction bytes are
reviewed separately from the generated decoder; no assembler premise is used. -/
namespace MachCSL.Machine.SpinlockImage
open MachCSL.Memory

def base : Int := 0x80000000
def lockAddress : PhysicalAddress := 0x80001000#64
def counterAddress : PhysicalAddress := 0x80001004#64

def code : List Byte := [
  0xf3#8, 0x22#8, 0x40#8, 0xf1#8,
  0x13#8, 0xb3#8, 0x22#8, 0x00#8,
  0x63#8, 0x0c#8, 0x03#8, 0x02#8,
  0x17#8, 0x15#8, 0x00#8, 0x00#8,
  0x13#8, 0x05#8, 0x45#8, 0xff#8,
  0x13#8, 0x07#8, 0x10#8, 0x00#8,
  0x93#8, 0x07#8, 0x07#8, 0x00#8,
  0xaf#8, 0x27#8, 0xf5#8, 0x0c#8,
  0x9b#8, 0x87#8, 0x07#8, 0x00#8,
  0xe3#8, 0x9a#8, 0x07#8, 0xfe#8,
  0x03#8, 0x28#8, 0x45#8, 0x00#8,
  0x1b#8, 0x08#8, 0x18#8, 0x00#8,
  0x23#8, 0x22#8, 0x05#8, 0x01#8,
  0x0f#8, 0x00#8, 0x10#8, 0x03#8,
  0x23#8, 0x20#8, 0x05#8, 0x00#8,
  0x6f#8, 0xf0#8, 0xdf#8, 0xfd#8,
  0x6f#8, 0x00#8, 0x00#8, 0x00#8
]

def word : Fin 17 → BitVec 32 := fun i =>
  match i.val with
  | 0 => 0xf14022f3#32
  | 1 => 0x0022b313#32
  | 2 => 0x02030c63#32
  | 3 => 0x00001517#32
  | 4 => 0xff450513#32
  | 5 => 0x00100713#32
  | 6 => 0x00070793#32
  | 7 => 0x0cf527af#32
  | 8 => 0x0007879b#32
  | 9 => 0xfe079ae3#32
  | 10 => 0x00452803#32
  | 11 => 0x0018081b#32
  | 12 => 0x01052223#32
  | 13 => 0x0310000f#32
  | 14 => 0x00052023#32
  | 15 => 0xfddff06f#32
  | _ => 0x0000006f#32

def image : BootImage where
  vector := BitVec.ofInt 64 base
  byte address := if base ≤ address ∧ address < base + 68 then
    code[(address - base).toNat]?.getD 0#8 else 0#8

def instructionAddress (i : Fin 17) : PhysicalAddress :=
  BitVec.ofInt 64 (base + 4 * (i.val : Int))

end MachCSL.Machine.SpinlockImage
