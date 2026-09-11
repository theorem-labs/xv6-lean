import Xv6.Kernel.KernelDatumDefs
import MachCSL.Logic.StackPhysicalDefs

/-! Source StackOwn.v: the virtual, context-indexed scratch stack. The exact
existential word list and downward modular addresses retain every mapping,
tier, byte and timestamp fact through the KernelDatum word. -/
namespace Xv6.Kernel.KernelStack
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := KernelDatum.Capacity
abbrev Tier := KernelDatum.Tier
abbrev paStk := StackPhysical.paStk

variable {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)

def words (tier : Tier) (ξ : TsoContext.CtxId) (sp : BitVec 64) (contents : List (BitVec 64)) : IProp GF :=
  iprop([∗list] i ↦ value ∈ contents,
    KernelDatum.word capacity era tier ξ (paStk sp (i + 1)) (.own 1) value)

def own (tier : Tier) (ξ : TsoContext.CtxId) (sp : BitVec 64) (depth : Nat) : IProp GF :=
  iprop(∃ contents, ⌜contents.length = depth⌝ ∗ words capacity era tier ξ sp contents)

end Xv6.Kernel.KernelStack
