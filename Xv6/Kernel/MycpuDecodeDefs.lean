import MachCSL.Machine.JalLoopPlanInstruction
import Xv6.Machine.Boot

namespace Xv6.Kernel.MycpuDecode
open MachCSL.Machine LeanPaperStock.Functions

/-- Concrete address from the pinned source, independently checked below against
actual image bytes. This definition does not certify ELF symbol parsing. -/
def base : Int := 0x800018ba
def cpusAddress : Int := 0x800123e8

def offset (i : Fin 14) : Nat :=
  match i.val with
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 6
  | 4 => 8
  | 5 => 10
  | 6 => 12
  | 7 => 14
  | 8 => 18
  | 9 => 22
  | 10 => 24
  | 11 => 26
  | 12 => 28
  | _ => 30

def width (i : Fin 14) : Nat :=
  match i.val with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 4
  | 8 => 4
  | 9 => 2
  | 10 => 2
  | 11 => 2
  | 12 => 2
  | _ => 2

def encoding (i : Fin 14) : Nat :=
  match i.val with
  | 0 => 0x1141
  | 1 => 0xe406
  | 2 => 0xe022
  | 3 => 0x800
  | 4 => 0x8792
  | 5 => 0x2781
  | 6 => 0x79e
  | 7 => 0x11517
  | 8 => 0xb2050513
  | 9 => 0x953e
  | 10 => 0x60a2
  | 11 => 0x6402
  | 12 => 0x141
  | _ => 0x8082

def decoded (i : Fin 14) : instruction :=
  match i.val with
  | 0 => .C_ADDI (48#6, .Regidx 2#5)
  | 1 => .C_SDSP (1#6, .Regidx 1#5)
  | 2 => .C_SDSP (0#6, .Regidx 8#5)
  | 3 => .C_ADDI4SPN (.Cregidx 0#3, 4#8)
  | 4 => .C_MV (.Regidx 15#5, .Regidx 4#5)
  | 5 => .C_ADDIW (0#6, .Regidx 15#5)
  | 6 => .C_SLLI (7#6, .Regidx 15#5)
  | 7 => .UTYPE (17#20, .Regidx 10#5, .AUIPC)
  | 8 => .ITYPE (0xb20#12, .Regidx 10#5, .Regidx 10#5, .ADDI)
  | 9 => .C_ADD (.Regidx 10#5, .Regidx 15#5)
  | 10 => .C_LDSP (1#6, .Regidx 1#5)
  | 11 => .C_LDSP (0#6, .Regidx 8#5)
  | 12 => .C_ADDI (16#6, .Regidx 2#5)
  | _ => .C_JR (.Regidx 1#5)

def normalized (i : Fin 14) : instruction :=
  match i.val with
  | 0 => .ITYPE (0xff0#12, .Regidx 2#5, .Regidx 2#5, .ADDI)
  | 1 => .STORE (8#12, .Regidx 1#5, .Regidx 2#5, 8)
  | 2 => .STORE (0#12, .Regidx 8#5, .Regidx 2#5, 8)
  | 3 => .ITYPE (16#12, .Regidx 2#5, .Regidx 8#5, .ADDI)
  | 4 => .RTYPE (.Regidx 4#5, .Regidx 0#5, .Regidx 15#5, .ADD)
  | 5 => .ADDIW (0#12, .Regidx 15#5, .Regidx 15#5)
  | 6 => .SHIFTIOP (7#6, .Regidx 15#5, .Regidx 15#5, .SLLI)
  | 7 => .UTYPE (17#20, .Regidx 10#5, .AUIPC)
  | 8 => .ITYPE (0xb20#12, .Regidx 10#5, .Regidx 10#5, .ADDI)
  | 9 => .RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 10#5, .ADD)
  | 10 => .LOAD (8#12, .Regidx 2#5, .Regidx 1#5, false, 8)
  | 11 => .LOAD (0#12, .Regidx 2#5, .Regidx 8#5, false, 8)
  | 12 => .ITYPE (16#12, .Regidx 2#5, .Regidx 2#5, .ADDI)
  | _ => .JALR (0#12, .Regidx 1#5, .Regidx 0#5)

def address (i : Fin 14) : MachCSL.Memory.PhysicalAddress := BitVec.ofInt 64 (base + offset i)
def compressed (i : Fin 14) : Bool := width i == 2
def word (i : Fin 14) : BitVec (8 * width i) := BitVec.ofNat _ (encoding i)
def decode (i : Fin 14) : SailM instruction :=
  if compressed i then ext_decode_compressed (BitVec.ofNat 16 (encoding i))
  else ext_decode (BitVec.ofNat 32 (encoding i))

/-- Sufficient concrete configuration for this first decode certificate. The
compressed decoder reads misa; base matching checks supervisor LPE via menvcfg.
The source's weaker misa.C-only compressed premise is recorded in STATUS. -/
def snapshot (i : Fin 14) : JalLoop.Snapshot :=
  if compressed i then fun r => match r with
    | .misa => some 0x800000000014112d#64
    | _ => none
  else fun r => match r with
    | .cur_privilege => some .Supervisor
    | .menvcfg => some 0xa000000000000000#64
    | _ => none

def Config (i : Fin 14) (rs : RegisterFile) : Prop :=
  if compressed i then rs .misa = 0x800000000014112d#64
  else rs .cur_privilege = .Supervisor ∧ rs .menvcfg = 0xa000000000000000#64

def bytes : List UInt8 := [0x41, 0x11, 0x6, 0xe4, 0x22, 0xe0, 0x0, 0x8, 0x92, 0x87, 0x81, 0x27, 0x9e, 0x7, 0x17, 0x15, 0x1, 0x0, 0x13, 0x5, 0x5, 0xb2, 0x3e, 0x95, 0xa2, 0x60, 0x2, 0x64, 0x41, 0x1, 0x82, 0x80]

end Xv6.Kernel.MycpuDecode
