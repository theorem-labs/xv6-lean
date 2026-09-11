import MachCSL.Logic.TsoContextStoreDefs
import MachCSL.Memory.ReadBytes

/-! Physical prerequisite of `TsoCtx.v:845–940` word ownership.
The source virtual translation/tier component is deliberately not asserted. -/
namespace MachCSL.Logic.TsoContextWord
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContext

abbrev Word := BitVec 64

def Aligned (a : PhysicalAddress) : Prop := a.toNat % 8 = 0

def pointsto {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)
    (ξ : CtxId) (a : PhysicalAddress) (dq : DFrac) (word : Word) : IProp GF :=
  iprop(⌜Aligned a⌝ ∗ [∗list] j ∈ List.range 8,
    physPointsto capacity names ξ (addressAdd a j) dq (nthByte word j))

def Readback (g : State) (cpu : CPU) (a : PhysicalAddress) (word : Word) : Prop :=
  ∀ view, g.views cpu ≤ view →
    ReadsBytes g.image g.log (hartAgent cpu) view a 8 word ∧
    readBytes (read g.image g.log (hartAgent cpu) view) a 8 = some word

end MachCSL.Logic.TsoContextWord
