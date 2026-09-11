import MachCSL.Logic.TsoContextDefs
import MachCSL.Memory.ReadBytes

/-! Exact physical context byte windows, with no alignment restriction. -/
namespace MachCSL.Logic.TsoContextBytes
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContext

def window {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)
    (ξ : CtxId) (a : PhysicalAddress) (n : Nat) (dq : DFrac) (word : BitVec (8 * n)) : IProp GF :=
  iprop([∗list] j ∈ List.range n,
    physPointsto capacity names ξ (addressAdd a j) dq (nthByte word j))

def Readback (g : State) (cpu : CPU) (a : PhysicalAddress) (n : Nat)
    (word : BitVec (8 * n)) : Prop :=
  ∀ view, g.views cpu ≤ view →
    ReadsBytes g.image g.log (hartAgent cpu) view a n word ∧
    readBytes (read g.image g.log (hartAgent cpu) view) a n = some word

end MachCSL.Logic.TsoContextBytes
