import Xv6.Kernel.KptFetchDefs
import Xv6.Kernel.KernelTextImageDefs
import Xv6.Kernel.PushOffMycpuCallsDefs

/-! Full CodePushOff.v listing. Decoded and normalized constructors record
source syntax only until separately checked against the generated decoder. -/
namespace Xv6.Kernel.PushOffCode
open Iris MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
abbrev Capacity := KptOwnership.Capacity
abbrev Index := Fin 24
def base : Int := Xv6.Generated.KernelMaps.Symbols.push_off

def offset (i : Index) : Nat :=
  match i.val with
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x8
  | 5 => 0xa
  | 6 => 0xe
  | 7 => 0x10
  | 8 => 0x14
  | 9 => 0x16
  | 10 => 0x18
  | 11 => 0x1c
  | 12 => 0x1e
  | 13 => 0x20
  | 14 => 0x22
  | 15 => 0x24
  | 16 => 0x26
  | 17 => 0x28
  | 18 => 0x2a
  | 19 => 0x2c
  | 20 => 0x30
  | 21 => 0x34
  | 22 => 0x36
  | _ => 0x38

def width (i : Index) : Nat :=
  match i.val with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 4
  | 6 => 2
  | 7 => 4
  | 8 => 2
  | 9 => 2
  | 10 => 4
  | 11 => 2
  | 12 => 2
  | 13 => 2
  | 14 => 2
  | 15 => 2
  | 16 => 2
  | 17 => 2
  | 18 => 2
  | 19 => 4
  | 20 => 4
  | 21 => 2
  | 22 => 2
  | _ => 2

def encoding (i : Index) : Nat :=
  match i.val with
  | 0 => 0x1101
  | 1 => 0xec06
  | 2 => 0xe822
  | 3 => 0xe426
  | 4 => 0x1000
  | 5 => 0x100177f3
  | 6 => 0x84be
  | 7 => 0x52b000ef
  | 8 => 0x5d3c
  | 9 => 0xcb99
  | 10 => 0x523000ef
  | 11 => 0x5d3c
  | 12 => 0x2785
  | 13 => 0xdd3c
  | 14 => 0x60e2
  | 15 => 0x6442
  | 16 => 0x64a2
  | 17 => 0x6105
  | 18 => 0x8082
  | 19 => 0x50f000ef
  | 20 => 0x14d793
  | 21 => 0x8b85
  | 22 => 0xdd7c
  | _ => 0xb7c5

def address (i : Index) : Int := base + offset i
def pc (i : Index) : BitVec 64 := KernelTextImage.address (address i)
def compressed (i : Index) : Bool := width i == 2
def result (i : Index) : FetchResult :=
  if compressed i then .F_RVC (BitVec.ofNat 16 (encoding i))
  else .F_Base (BitVec.ofNat 32 (encoding i))

def decoded (i : Index) : instruction :=
  match i.val with
  | 0 => .C_ADDI (32#6, .Regidx 2#5)
  | 1 => .C_SDSP (3#6, .Regidx 1#5)
  | 2 => .C_SDSP (2#6, .Regidx 8#5)
  | 3 => .C_SDSP (1#6, .Regidx 9#5)
  | 4 => .C_ADDI4SPN (.Cregidx 0#3, 8#8)
  | 5 => .CSRImm (256#12, 2#5, .Regidx 15#5, .CSRRC)
  | 6 => .C_MV (.Regidx 9#5, .Regidx 15#5)
  | 7 => .JAL (3370#21, .Regidx 1#5)
  | 8 => .C_LW (30#5, .Cregidx 2#3, .Cregidx 7#3)
  | 9 => .C_BEQZ (11#8, .Cregidx 7#3)
  | 10 => .JAL (3362#21, .Regidx 1#5)
  | 11 => .C_LW (30#5, .Cregidx 2#3, .Cregidx 7#3)
  | 12 => .C_ADDIW (1#6, .Regidx 15#5)
  | 13 => .C_SW (30#5, .Cregidx 2#3, .Cregidx 7#3)
  | 14 => .C_LDSP (3#6, .Regidx 1#5)
  | 15 => .C_LDSP (2#6, .Regidx 8#5)
  | 16 => .C_LDSP (1#6, .Regidx 9#5)
  | 17 => .C_ADDI16SP 2#6
  | 18 => .C_JR (.Regidx 1#5)
  | 19 => .JAL (3342#21, .Regidx 1#5)
  | 20 => .SHIFTIOP (1#6, .Regidx 9#5, .Regidx 15#5, .SRLI)
  | 21 => .C_ANDI (1#6, .Cregidx 7#3)
  | 22 => .C_SW (31#5, .Cregidx 2#3, .Cregidx 7#3)
  | _ => .C_J 2032#11

def normalized (i : Index) : instruction :=
  match i.val with
  | 0 => .ITYPE (0xfe0#12, .Regidx 2#5, .Regidx 2#5, .ADDI)
  | 1 => .STORE (24#12, .Regidx 1#5, .Regidx 2#5, 8)
  | 2 => .STORE (16#12, .Regidx 8#5, .Regidx 2#5, 8)
  | 3 => .STORE (8#12, .Regidx 9#5, .Regidx 2#5, 8)
  | 4 => .ITYPE (32#12, .Regidx 2#5, .Regidx 8#5, .ADDI)
  | 5 => .CSRImm (256#12, 2#5, .Regidx 15#5, .CSRRC)
  | 6 => .RTYPE (.Regidx 15#5, .Regidx 0#5, .Regidx 9#5, .ADD)
  | 7 => .JAL (3370#21, .Regidx 1#5)
  | 8 => .LOAD (120#12, .Regidx 10#5, .Regidx 15#5, false, 4)
  | 9 => .BTYPE (22#13, .Regidx 0#5, .Regidx 15#5, .BEQ)
  | 10 => .JAL (3362#21, .Regidx 1#5)
  | 11 => .LOAD (120#12, .Regidx 10#5, .Regidx 15#5, false, 4)
  | 12 => .ADDIW (1#12, .Regidx 15#5, .Regidx 15#5)
  | 13 => .STORE (120#12, .Regidx 15#5, .Regidx 10#5, 4)
  | 14 => .LOAD (24#12, .Regidx 2#5, .Regidx 1#5, false, 8)
  | 15 => .LOAD (16#12, .Regidx 2#5, .Regidx 8#5, false, 8)
  | 16 => .LOAD (8#12, .Regidx 2#5, .Regidx 9#5, false, 8)
  | 17 => .ITYPE (32#12, .Regidx 2#5, .Regidx 2#5, .ADDI)
  | 18 => .JALR (0#12, .Regidx 1#5, .Regidx 0#5)
  | 19 => .JAL (3342#21, .Regidx 1#5)
  | 20 => .SHIFTIOP (1#6, .Regidx 9#5, .Regidx 15#5, .SRLI)
  | 21 => .ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ANDI)
  | 22 => .STORE (124#12, .Regidx 15#5, .Regidx 10#5, 4)
  | _ => .JAL (0x1fffe0#21, .Regidx 0#5)

/-- Ownership footprint, including the aligned compressed lookahead. Base
instructions keep four bytes even when actual fetch uses two half reads. -/
def fetchWidth (i : Index) : Nat :=
  if width i = 4 ∨ is_aligned_vaddr (.Virtaddr (pc i)) 4 = true then 4 else 2

def fetchEncoding (i : Index) : Nat :=
  match i.val with
  | 0 => 0xec061101
  | 1 => 0xec06
  | 2 => 0xe426e822
  | 3 => 0xe426
  | 4 => 0x77f31000
  | 5 => 0x100177f3
  | 6 => 0x84be
  | 7 => 0x52b000ef
  | 8 => 0xcb995d3c
  | 9 => 0xcb99
  | 10 => 0x523000ef
  | 11 => 0x27855d3c
  | 12 => 0x2785
  | 13 => 0x60e2dd3c
  | 14 => 0x60e2
  | 15 => 0x64a26442
  | 16 => 0x64a2
  | 17 => 0x80826105
  | 18 => 0x8082
  | 19 => 0x50f000ef
  | 20 => 0x14d793
  | 21 => 0xdd7c8b85
  | 22 => 0xdd7c
  | _ => 0x1101b7c5

def fetchWord (i : Index) : BitVec (8 * fetchWidth i) := BitVec.ofNat _ (fetchEncoding i)
/-- The first58 bytes are push_off; the final two are acquire's actual first
instruction. They are needed by the final aligned compressed fetch. -/
def bytes : List UInt8 := [0x1, 0x11, 0x6, 0xec, 0x22, 0xe8, 0x26, 0xe4, 0x0, 0x10, 0xf3, 0x77, 0x1, 0x10, 0xbe, 0x84, 0xef, 0x0, 0xb0, 0x52, 0x3c, 0x5d, 0x99, 0xcb, 0xef, 0x0, 0x30, 0x52, 0x3c, 0x5d, 0x85, 0x27, 0x3c, 0xdd, 0xe2, 0x60, 0x42, 0x64, 0xa2, 0x64, 0x5, 0x61, 0x82, 0x80, 0xef, 0x0, 0xf0, 0x50, 0x93, 0xd7, 0x14, 0x0, 0x85, 0x8b, 0x7c, 0xdd, 0xc5, 0xb7, 0x1, 0x11]
def callIndex (site : PushOffMycpuCalls.Site) : Index :=
  if site.val = 0 then ⟨7, by decide⟩ else if site.val = 1 then ⟨10, by decide⟩ else ⟨19, by decide⟩

end Xv6.Kernel.PushOffCode
