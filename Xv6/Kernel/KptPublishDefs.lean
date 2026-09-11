import Xv6.Kernel.KptSharedDefs
import MachCSL.Logic.ContextPinMintDefs

/-! Source KptPublish.v: physical context-to-kernel publication using the same
machine capacities and era names as the existing tree ownership and shared
invariant. The tree is transformed; a pinned replacement is never assumed. -/
noncomputable section
namespace Xv6.Kernel.KptPublish
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := KptOwnership.Capacity
abbrev CtxId := TsoContext.CtxId
abbrev Tree := PtTree.Tree

@[reducible] def contextCapacity {GF : BundledGFunctors} (capacity : Capacity GF) :
    ContextPinMint.Capacity GF := TsoContextReadWP.contextCapacity capacity.machine
@[reducible] def contextNames (era : Era.Record) : ContextPinMint.Names :=
  TsoContextReadWP.contextNames era

variable {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)

abbrev heapAt (g : State) : IProp GF :=
  TsoContext.heapAt (contextCapacity capacity) (contextNames era) g
abbrev tsoAt (g : State) : IProp GF :=
  Tso.Interp.tsoInterpAt capacity.machine.era.tso era.tsoNames era.imageBytes g
abbrev running (cpu : CPU) (ξ : CtxId) : IProp GF :=
  TsoContextReadWP.running capacity.machine era cpu ξ
abbrev viewZero (B : Nat) : IProp GF :=
  Tso.Views.viewLB capacity.machine.era.views era.views era.logLength 0 B
abbrev viewHart (cpu : CPU) (B : Nat) : IProp GF :=
  Tso.Views.viewLB capacity.machine.era.views era.views era.logLength (hartAgent cpu) B
abbrev logBound (B : Nat) : IProp GF :=
  Tso.Views.llb capacity.machine.era.views era.logLength B

/-- The source generic ordered slot-list fold; instantiated by the existing
512-index page enumeration. Repetitions/empty lists are not ruled out. -/
def slotsOwn {α : Type} (tier : KptOwnership.Tier) (indices : List α)
    (address : α → PhysicalAddress) (word : α → BitVec 64) : IProp GF :=
  iprop([∗list] i ∈ indices, KptOwnership.slotOwn capacity era tier (address i) (.own 1) (word i))

end Xv6.Kernel.KptPublish
