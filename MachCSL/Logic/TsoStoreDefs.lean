import MachCSL.Logic.HeapDefs
import MachCSL.Logic.TsoAppendDefs

/-! Full native physical ledger store, `TsoCtx.ledger_store_ok`. This component
updates ghost resources for explicit physical successor equations; it is not a
machine event WP and does not choose which operational successor occurs. -/
namespace MachCSL.Logic.TsoStore
variable {bits : Nat}
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

structure Capacity (GF : BundledGFunctors) where
  heap : Heap.Capacity GF
  views : Tso.Views.Capacity GF
  history : Tso.History.Capacity GF

@[reducible] def Capacity.tso {GF : BundledGFunctors} (c : Capacity GF) : Tso.Interp.Capacity GF :=
  ⟨c.heap.ledger, c.views, c.history⟩

structure Names where
  tso : Tso.Interp.EraNames
  metadata : GName

@[reducible] def Names.heap (names : Names) : Heap.Names := ⟨names.tso.ledger.bytes, names.metadata⟩

def SameDomain (old new : Tso.AddressMap Byte) : Prop :=
  Iris.Std.PartialMap.dom old = Iris.Std.PartialMap.dom new

structure Transition (before after : State) (new : Tso.AddressMap Byte) (author : Agent) : Prop where
  image : after.image = before.image
  log : after.log = before.log ++ [⟨FiniteMap.decode new, author⟩]
  memory : after.memory = overlay (FiniteMap.decode new) before.memory
  viewsMono : ∀ cpu, before.views cpu ≤ after.views cpu
  viewsBound : ∀ cpu, after.views cpu ≤ after.log.length

/-- The source's right-fold snapshot, as a finite map. Its decoder agrees for
every size, including accesses that wrap repeatedly. -/
def windowMap (a : PhysicalAddress) (n : Nat) (word : BitVec bits) : Tso.AddressMap Byte :=
  Iris.Std.PartialMap.ofList ((List.range n).map (fun j => (addressAdd a j, nthByte word j)))

structure WindowTransition (before after : State) (a : PhysicalAddress) (n : Nat)
    (word : BitVec bits) (author : Agent) : Prop where
  image : after.image = before.image
  log : after.log = before.log ++ [⟨snapshot a n word, author⟩]
  memory : after.memory = writeBytes before.memory a n word
  viewsMono : ∀ cpu, before.views cpu ≤ after.views cpu
  viewsBound : ∀ cpu, after.views cpu ≤ after.log.length

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def ledgerByte (names : Names) (a : PhysicalAddress) (byte : Byte) : IProp GF :=
  iprop(Tso.physBytePointsto capacity.heap.ledger names.tso.ledger.bytes a (.own 1) byte ∗
    ∃ time : Nat, Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps (.own 1) a (time, Tso.payNone))

def ledgerMap (names : Names) (old : Tso.AddressMap Byte) : IProp GF :=
  iprop([∗map] a ↦ byte ∈ old, ledgerByte capacity names a byte)

def storedByte (names : Names) (a : PhysicalAddress) (byte : Byte) (time : Nat) : IProp GF :=
  iprop(Tso.physBytePointsto capacity.heap.ledger names.tso.ledger.bytes a (.own 1) byte ∗
    Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps (.own 1) a (time, Tso.payNone))

def storedMap (names : Names) (new : Tso.AddressMap Byte) (time : Nat) : IProp GF :=
  iprop([∗map] a ↦ byte ∈ new, storedByte capacity names a byte time)

def ledgerWindow (names : Names) (a : PhysicalAddress) (n : Nat) (word : BitVec bits) : IProp GF :=
  iprop([∗list] j ∈ List.range n, ledgerByte capacity names (addressAdd a j) (nthByte word j))

def storedWindow (names : Names) (a : PhysicalAddress) (n : Nat) (word : BitVec bits)
    (time : Nat) : IProp GF :=
  iprop([∗list] j ∈ List.range n, storedByte capacity names (addressAdd a j) (nthByte word j) time)

def heapAt (names : Names) (memory : ByteMap 64) : IProp GF :=
  iprop(∃ representation : Tso.AddressMap Byte,
    Heap.interp capacity.heap names.heap representation ∗ ⌜FiniteMap.decode representation = memory⌝)

end MachCSL.Logic.TsoStore
