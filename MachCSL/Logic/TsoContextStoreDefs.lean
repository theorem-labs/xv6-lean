import MachCSL.Logic.TsoContextDefs

/-! Registered physical context store, `TsoCtx.v:2572–2587`.
The larger visibility-free `phys_free` gate is not claimed here. -/
namespace MachCSL.Logic.TsoContextStore
open Iris Iris.BI MachCSL.Memory MachCSL.Machine
open TsoContext

/-- Every old dirty entry is retained; each written address is registered at
one shared timestamp. This is ghost bookkeeping, not one message per byte. -/
def registerEntries (old : Tso.History.DirtySet) (time : Nat) :
    List (PhysicalAddress × Byte) → Tso.History.DirtySet
  | [] => old
  | entry :: rest => registerEntries old time rest ∪ {(time, entry.1)}

def registerDirty (old : Tso.History.DirtySet) (time : Nat) (new : Tso.AddressMap Byte) :
    Tso.History.DirtySet := registerEntries old time (Iris.Std.FiniteMap.toList new)

def physMap {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)
    (ξ : CtxId) (memory : Tso.AddressMap Byte) : IProp GF :=
  iprop([∗map] a ↦ byte ∈ memory, physPointsto capacity names ξ a (.own 1) byte)

/-- The ordinary store's TSO fields. Other machine fields are unconstrained
here because the resource gate does not own their interpretations. -/
structure OrdinaryTransition (before after : State) (new : Tso.AddressMap Byte) (cpu : CPU) : Prop where
  image : after.image = before.image
  log : after.log = before.log ++ [⟨FiniteMap.decode new, hartAgent cpu⟩]
  memory : after.memory = overlay (FiniteMap.decode new) before.memory
  views : after.views = before.views

end MachCSL.Logic.TsoContextStore
