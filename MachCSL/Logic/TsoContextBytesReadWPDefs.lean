import MachCSL.Logic.TsoContextBytesDefs
import MachCSL.Logic.TsoContextReadWPDefs

namespace MachCSL.Logic.TsoContextBytesReadWP
open Iris MachCSL.Machine
abbrev contextCapacity := @TsoContextReadWP.contextCapacity
abbrev contextNames := TsoContextReadWP.contextNames
abbrev running := @TsoContextReadWP.running
abbrev window {GF : BundledGFunctors} (capacity : MachineInterp.Capacity GF)
    (era : Era.Record) (ξ : TsoContext.CtxId) (a : Memory.PhysicalAddress)
    (n : Nat) (dq : DFrac) (word : BitVec (8 * n)) : IProp GF :=
  TsoContextBytes.window (contextCapacity capacity) (contextNames era) ξ a n dq word
end MachCSL.Logic.TsoContextBytesReadWP
