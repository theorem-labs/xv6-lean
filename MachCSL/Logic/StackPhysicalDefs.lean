import MachCSL.Logic.TsoContextWordDefs

/-! Physical word component of `StackOwn.v:45–57,151–315`.
This does not include the source virtual translation or kernel-tier assertions. -/
namespace MachCSL.Logic.StackPhysical
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContext

/-- Source `pa_stk`: subtraction is modular, for every natural depth. -/
def paStk (sp : PhysicalAddress) (depth : Nat) : PhysicalAddress :=
  sp - BitVec.ofNat 64 (8 * depth)

def words {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)
    (ξ : CtxId) (sp : PhysicalAddress) (contents : List TsoContextWord.Word) : IProp GF :=
  iprop([∗list] i ↦ word ∈ contents,
    TsoContextWord.pointsto capacity names ξ (paStk sp (i + 1)) (.own 1) word)

/-- Exact source existential contents and length, using physical word ownership. -/
def own {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)
    (ξ : CtxId) (sp : PhysicalAddress) (depth : Nat) : IProp GF :=
  iprop(∃ contents, ⌜contents.length = depth⌝ ∗ words capacity names ξ sp contents)

end MachCSL.Logic.StackPhysical
