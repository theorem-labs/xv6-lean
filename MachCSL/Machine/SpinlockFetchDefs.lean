import MachCSL.Machine.SpinlockImageProofs
import MachCSL.Machine.JalLoopUniversalFetch

namespace MachCSL.Machine.SpinlockFetch
open MachCSL.Logic.EventWP

abbrev Static (index : Fin 17) := BootUniversal.StaticBoot (SpinlockImage.instructionAddress index)

def CodeRead (index : Fin 17) (n : Nat) (req : Logic.MemoryReadWP.ReadRequest n)
    (word : BitVec (8 * n)) : Prop :=
  n = 4 ∧ req.pa = SpinlockImage.instructionAddress index ∧
    word = BitVec.ofNat (8 * n) (SpinlockImage.word index).toNat

end MachCSL.Machine.SpinlockFetch
