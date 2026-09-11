import MachCSL.Machine.SpinlockAccessDefs
import MachCSL.Machine.BootHartIdProofs

namespace MachCSL.Machine.SpinlockCore

/-- The boot fields retained by this program, independently of PC and operands. -/
structure Core (cpu : CPU) (rs : RegisterFile) : Prop extends SpinlockAccess.Static rs where
  mie : rs .mie = 0#64
  mideleg : rs .mideleg = 0#64
  elp : rs .elp = 0#1
  hartState : rs .hart_state = .HART_ACTIVE ()
  off : BootPmp.Off rs
  hartid : rs .mhartid = BitVec.ofNat 64 cpu.val

/-- Registers changed by the integration program, its cycle wrapper or PLIC. -/
def Writable : Register → Prop
  | .PC | .nextPC | .x5 | .x6 | .x10 | .x14 | .x15 | .x16
  | .minstret | .minstret_increment | .mcycle | .mtime | .mip
  | .sig_meip | .sig_seip => True
  | _ => False

end MachCSL.Machine.SpinlockCore
