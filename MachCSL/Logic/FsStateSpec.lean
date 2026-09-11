import MachCSL.Logic.FsStateDefs

namespace MachCSL.Logic.FsState
open Iris Iris.Std Iris.BI Xv6.Fs FsView

/-- The bounded native hierarchy interface. Allocation and transfer are
separate later theorems; this structure does not assume either. -/
structure ResourceSpec {GF : BundledGFunctors} (view : View GF)
    (capacity : FsLink.Capacity GF) : Prop where
  inodeLocal : ∀ sb i n, inodeOwned view capacity sb i n ⊢ ⌜DurableNode.Local i n⌝
  geometry : ∀ dq s, state view capacity dq s ⊢ ⌜DurableState.Geometry s⌝
  factoring : ∀ dq s, state view capacity dq s ⊣⊢ footprint view dq s ∗ ghost view capacity s
  byteShare : ∀ dq s, state view capacity dq s = state (gammaQ view dq) capacity (.own 1) s
  ghostShare : ∀ dq i n, inodeGhost (gammaQ view dq) capacity i n = inodeGhost view capacity i n

end MachCSL.Logic.FsState
