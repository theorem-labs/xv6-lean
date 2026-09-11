import MachCSL.Logic.TsoViewsDefs
import Iris.Algebra.LeibnizSet
import Iris.Std.GenSetsInstances

/-! Remaining `TsoGhost.v` resources: monotone dirty sets and persistent log entries. -/
namespace MachCSL.Logic.Tso.History
open MachCSL.Memory Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI Auth

abbrev DirtyKey := Nat × PhysicalAddress
attribute [local instance] lexOrd
abbrev DirtySet := _root_.Std.ExtTreeSet DirtyKey
abbrev DirtyUR := LeibnizSet DirtySet
abbrev DirtyRF := constOF (Auth DirtyUR)
abbrev LogMap (V : Type) := _root_.Std.ExtTreeMap Nat V
abbrev LogRA := HeapView Nat (Agree (DiscreteO (Message 64))) LogMap
abbrev LogRF := constOF LogRA

def dirtyFunctor : GFunctor := ⟨DirtyRF, inferInstance⟩
def logFunctor : GFunctor := ⟨LogRF, inferInstance⟩

/-- Resource capacity only; every assertion takes its runtime names explicitly. -/
structure Capacity (GF : BundledGFunctors) where
  logs : GhostMapG GF Nat (Message 64) LogMap
  dirty : ElemG GF DirtyRF

inductive Slot where
  | logs
  | dirty
  deriving DecidableEq

def Slot.index : Slot → Nat
  | .logs => 4
  | .dirty => 5

theorem Slot.index_injective {a b : Slot} (h : a.index = b.index) : a = b := by
  cases a <;> cases b <;> simp_all [index]

/-- Extends the four-slot view registry without introducing another mono-nat. -/
def registry : BundledGFunctors :=
  (Views.registry.set Slot.logs.index logFunctor).set Slot.dirty.index dirtyFunctor

theorem registry_old (i : Nat) (h : i < 4) : registry i = Views.registry i := by
  simp [registry, BundledGFunctors.set, Slot.index, show i ≠ 4 by omega, show i ≠ 5 by omega]

theorem registry_unused (i : Nat) (h : 6 ≤ i) : registry i = Views.registry i := by
  simp [registry, BundledGFunctors.set, Slot.index, show i ≠ 4 by omega, show i ≠ 5 by omega]

@[reducible] def logSlot : ElemG registry LogRF := ⟨4, rfl⟩
@[reducible] def dirtySlot : ElemG registry DirtyRF := ⟨5, rfl⟩
def registryCapacity : Capacity registry := ⟨⟨logSlot⟩, dirtySlot⟩
def viewsCapacity : Views.Capacity registry := ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩
def ledgerCapacity : Tso.Capacity registry := ⟨⟨⟨0, rfl⟩⟩, ⟨⟨1, rfl⟩⟩⟩

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def dsetAuth (γ : GName) (q : Qp) (set : DirtySet) : IProp GF :=
  iOwn (E := capacity.dirty) γ (●{DFrac.own q} LeibnizSet.valid set)
def dsetIn (γ : GName) (key : DirtyKey) : IProp GF :=
  iOwn (E := capacity.dirty) γ (◯ (LeibnizSet.valid {key} : DirtyUR))

def logAuth (γ : GName) (dq : DFrac) (entries : LogMap (Message 64)) : IProp GF :=
  letI := capacity.logs
  ghost_map_auth γ dq entries

def logElem (γ : GName) (index : Nat) (message : Message 64) : IProp GF :=
  letI := capacity.logs
  ghost_map_elem γ .discard index message

/-- Exact source `dirty_ok`; the author branch says nothing about the key's address. -/
def dirtyOK (γlog : GName) (h : Agent) (bound : Nat) (key : DirtyKey) : IProp GF :=
  iprop(⌜key.1 ≤ bound⌝ ∨ ∃ i m,
    ⌜key.1 = i + 1⌝ ∗ logElem capacity γlog i m ∗ ⌜m.author = h⌝)

/-- The finite map represents exactly the zero-indexed message list. -/
def LogRep (entries : LogMap (Message 64)) (log : WriteLog 64) : Prop :=
  ∀ i, PartialMap.get? entries i = log[i]?

end MachCSL.Logic.Tso.History
