import MachCSL.Logic.TsoContextWordDefs
import MachCSL.Logic.TsoPinnedReadDefs

/-! Native physical publication prerequisites of `CtxPinMint.v` and the boot
arm of `KptPublish.v`. The existing heap, timestamp, history and view names are
shared structurally. No new camera, context allocation or page tree is used. -/
namespace MachCSL.Logic.ContextPinMint
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

abbrev Capacity := TsoContext.Capacity
abbrev Names := TsoContext.Names
abbrev CtxId := TsoContext.CtxId

/-- Only this hart's publications must be visible. Other harts may have later
messages; this is not a whole-log drain. -/
def Drained (cpu : CPU) (g : State) : Prop :=
  ownPub (hartAgent cpu) g.log ≤ g.views cpu

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def contextBit (ξ : CtxId) (time : Nat) (a : PhysicalAddress) : IProp GF :=
  iprop(TsoContext.floor capacity ξ time ∨
    Tso.History.dsetIn capacity.history ξ.dirty (time, a))

def contextBytes (names : Names) (ξ : CtxId) (a : PhysicalAddress)
    (n : Nat) (value : Nat → Byte) : IProp GF :=
  iprop([∗list] j ∈ List.range n,
    TsoContext.physPointsto capacity names ξ (addressAdd a j) (.own 1) (value j))

def pinnedBytes (names : Names) (a : PhysicalAddress) (n : Nat)
    (value : Nat → Byte) (bound : Nat) (sets : Nat → Tso.ByteSet) : IProp GF :=
  iprop([∗list] j ∈ List.range n, ∃ time : Nat,
    Tso.physLedgerPin capacity.heap.ledger names.tso.ledger (addressAdd a j)
      (.own 1) (value j) time bound (sets j))

def pinnedWord (names : Names) (a : PhysicalAddress) (word : BitVec 64)
    (bound : Nat) (sets : Nat → Tso.ByteSet) : IProp GF :=
  iprop(⌜TsoContextWord.Aligned a⌝ ∗
    pinnedBytes capacity names a 8 (nthByte word) bound sets)

def bootByte (names : Names) (g : State) (a : PhysicalAddress)
    (byte : Byte) (allowed : Tso.ByteSet) : IProp GF :=
  iprop(∃ (floor time : Nat), ⌜floor ≤ g.log.length⌝ ∗
    Tso.physLedgerPin capacity.heap.ledger names.tso.ledger a (.own 1) byte time floor allowed ∗
    TsoPinnedRead.slotAnchor capacity.tso names.tso a floor)

def bootBytes (names : Names) (g : State) (a : PhysicalAddress) (n : Nat)
    (value : Nat → Byte) (sets : Nat → Tso.ByteSet) : IProp GF :=
  TsoPinnedRead.slotBytes capacity.tso names.tso a n (.own 1) value g.log.length sets

def bootWord (names : Names) (g : State) (a : PhysicalAddress) (word : BitVec 64)
    (sets : Nat → Tso.ByteSet) : IProp GF :=
  iprop(⌜TsoContextWord.Aligned a⌝ ∗ bootBytes capacity names g a 8 (nthByte word) sets)

end MachCSL.Logic.ContextPinMint
