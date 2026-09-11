import MachCSL.Logic.TsoPinnedReadDefs
import MachCSL.Logic.MemoryExclusiveWPDefs
import MachCSL.Machine.PteCanonicalDefs

namespace MachCSL.Logic.TsoPinnedReadWP
open Iris MachCSL.Memory MachCSL.Machine

variable {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF) (era : Era.Record)

abbrev credential (cpu : CPU) (bound : Nat) : IProp GF :=
  TsoPinnedRead.bootCredential capacity.era.tso era.tsoNames cpu bound
abbrev slot (a : PhysicalAddress) (n : Nat) (dq : DFrac) (value : Nat → Byte)
    (bound : Nat) (sets : Nat → Tso.ByteSet) : IProp GF :=
  TsoPinnedRead.slotBytes capacity.era.tso era.tsoNames a n dq value bound sets

def Allowed (n : Nat) (sets : Nat → Tso.ByteSet) (word : BitVec (8 * n)) : Prop :=
  ∀ j, j < n → nthByte word j ∈ sets j

end MachCSL.Logic.TsoPinnedReadWP
