import MachCSL.Logic.TsoStoreDefs
import MachCSL.Logic.TsoPredicates

/-! Registered-pin store, `TsoCtx.v:3517–3620,4190–4274`.
The source floor and allowed set survive each byte's own write-back. -/
namespace MachCSL.Logic.TsoPinnedStore
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

abbrev Capacity := TsoStore.Capacity
abbrev Names := TsoStore.Names

def storeTimestamps (new : Tso.AddressMap Byte) (time : Nat)
    (floors : PhysicalAddress → Nat) (sets : PhysicalAddress → Tso.ByteSet) :
    Tso.AddressMap Tso.TimestampElem :=
  new.map (fun a _ => (time, Tso.payPin (sets a) (floors a)))

/-- Std union is right biased: only actual written keys are replaced. -/
def appendTimestamps (old : Tso.AddressMap Tso.TimestampElem) (new : Tso.AddressMap Byte)
    (oldLength : Nat) (floors : PhysicalAddress → Nat) (sets : PhysicalAddress → Tso.ByteSet) :
    Tso.AddressMap Tso.TimestampElem :=
  old ∪ storeTimestamps new (oldLength + 1) floors sets

variable {bits : Nat}
variable {GF : BundledGFunctors} (capacity : Capacity GF)

abbrev pinMap (names : Names) (memory : Tso.AddressMap Byte) (dq : DFrac)
    (floors : PhysicalAddress → Nat) (sets : PhysicalAddress → Tso.ByteSet) : IProp GF :=
  Tso.pinMapOwn capacity.heap.ledger names.tso.ledger memory dq floors sets

def storedMap (names : Names) (memory : Tso.AddressMap Byte) (time : Nat)
    (floors : PhysicalAddress → Nat) (sets : PhysicalAddress → Tso.ByteSet) : IProp GF :=
  iprop([∗map] a ↦ byte ∈ memory,
    Tso.physLedgerPin capacity.heap.ledger names.tso.ledger a (.own 1) byte time (floors a) (sets a))

def pinWindow (names : Names) (a : PhysicalAddress) (n : Nat) (word : BitVec bits) (dq : DFrac)
    (floors : Nat → Nat) (sets : Nat → Tso.ByteSet) : IProp GF :=
  iprop([∗list] j ∈ List.range n, ∃ time : Nat,
    Tso.physLedgerPin capacity.heap.ledger names.tso.ledger (addressAdd a j) dq
      (nthByte word j) time (floors j) (sets j))

def storedWindow (names : Names) (a : PhysicalAddress) (n : Nat) (word : BitVec bits) (time : Nat)
    (floors : Nat → Nat) (sets : Nat → Tso.ByteSet) : IProp GF :=
  iprop([∗list] j ∈ List.range n,
    Tso.physLedgerPin capacity.heap.ledger names.tso.ledger (addressAdd a j) (.own 1)
      (nthByte word j) time (floors j) (sets j))

end MachCSL.Logic.TsoPinnedStore
