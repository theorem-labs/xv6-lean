import MachCSL.Machine.SpinlockImageDefs
import MachCSL.Machine.JalLoopPlanInstruction

namespace MachCSL.Machine.SpinlockDecode
open LeanPaperStock.Functions

/-- The actual decoder checks privilege/security for Zicfilp and reads `misa.A`
when checking the AMO encoding. Every supplied register must be covered by the
register file in the soundness theorem. -/
def decodeSnapshot : JalLoop.Snapshot
  | .misa => some 0x800000000014112d#64
  | r => JalLoop.decodeSnapshot r

/-- Expected ASTs for all seventeen words, separate from actual decoding. -/
def instruction (i : Fin 17) : instruction :=
  match i.val with
  | 0 => .CSRReg (0xf14#12, .Regidx 0#5, .Regidx 5#5, .CSRRS)
  | 1 => .ITYPE (2#12, .Regidx 5#5, .Regidx 6#5, .SLTIU)
  | 2 => .BTYPE (0x38#13, .Regidx 0#5, .Regidx 6#5, .BEQ)
  | 3 => .UTYPE (1#20, .Regidx 10#5, .AUIPC)
  | 4 => .ITYPE (0xff4#12, .Regidx 10#5, .Regidx 10#5, .ADDI)
  | 5 => .ITYPE (1#12, .Regidx 0#5, .Regidx 14#5, .ADDI)
  | 6 => .ITYPE (0#12, .Regidx 14#5, .Regidx 15#5, .ADDI)
  | 7 => .AMO (.AMOSWAP, true, false, .Regidx 15#5, .Regidx 10#5, 4, .Regidx 15#5)
  | 8 => .ADDIW (0#12, .Regidx 15#5, .Regidx 15#5)
  | 9 => .BTYPE (0x1ff4#13, .Regidx 0#5, .Regidx 15#5, .BNE)
  | 10 => .LOAD (4#12, .Regidx 10#5, .Regidx 16#5, false, 4)
  | 11 => .ADDIW (1#12, .Regidx 16#5, .Regidx 16#5)
  | 12 => .STORE (4#12, .Regidx 16#5, .Regidx 10#5, 4)
  | 13 => .FENCE (0#4, 3#4, 1#4, .Regidx 0#5, .Regidx 0#5)
  | 14 => .STORE (0#12, .Regidx 0#5, .Regidx 10#5, 4)
  | 15 => .JAL (0x1fffdc#21, .Regidx 0#5)
  | _ => .JAL (0#21, .Regidx 0#5)

end MachCSL.Machine.SpinlockDecode
