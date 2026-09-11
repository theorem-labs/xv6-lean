import MachCSL.Logic.TsoStoreDefs

/-! Running-context ownership and physical bytes, `TsoCtx.v:244–305,2095–2101`.
No translation, stack, context migration, or instruction contract is assumed. -/
namespace MachCSL.Logic.TsoContext
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

abbrev Capacity := TsoStore.Capacity
abbrev Names := TsoStore.Names

/-- Two runtime names, independent of any functor registry or assertion. -/
structure CtxId where
  bound : GName
  dirty : GName
  deriving DecidableEq

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def ctxAt (ξ : CtxId) (q : Qp) (bound : Nat) (dirty : Tso.History.DirtySet) : IProp GF :=
  iprop(Tso.Views.natAuth capacity.views ξ.bound (.own q) bound ∗
    Tso.History.dsetAuth capacity.history ξ.dirty q dirty)

def ownContext (names : Names) (cpu : CPU) (ξ : CtxId) : IProp GF :=
  iprop(∃ (B K W : Nat) (D : Tso.History.DirtySet),
    ctxAt capacity ξ 1 B D ∗
    Tso.Views.viewLB capacity.views names.tso.views names.tso.logLength (hartAgent cpu) K ∗
    ⌜B ≤ K⌝ ∗ Tso.Views.llb capacity.views names.tso.logLength W ∗
    ⌜∀ key ∈ D, key.1 ≤ W⌝ ∗
    [∗set] key ∈ D, Tso.History.dirtyOK capacity.history names.tso.logEntries (hartAgent cpu) B key)

def floor (ξ : CtxId) (bound : Nat) : IProp GF :=
  Tso.Views.llb capacity.views ξ.bound bound

def physPointsto (names : Names) (ξ : CtxId) (a : PhysicalAddress)
    (dq : DFrac) (byte : Byte) : IProp GF :=
  iprop(∃ time : Nat,
    Tso.physBytePointsto capacity.heap.ledger names.tso.ledger.bytes a dq byte ∗
    Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps dq a (time, Tso.payNone) ∗
    (floor capacity ξ time ∨ Tso.History.dsetIn capacity.history ξ.dirty (time, a)))

/-- The entire actual native gen_heap, including its metadata. -/
def heapAt (names : Names) (g : State) : IProp GF :=
  iprop(∃ memory : Tso.AddressMap Byte,
    Heap.interp capacity.heap names.heap memory ∗ ⌜FiniteMap.decode memory = g.memory⌝)

end MachCSL.Logic.TsoContext
