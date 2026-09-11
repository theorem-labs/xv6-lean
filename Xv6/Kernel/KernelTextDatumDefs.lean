import Xv6.Kernel.KernelDatumDefs
import MachCSL.Logic.TsoReadDefs
import MachCSL.Logic.TsoContextBytesDefs

/-! Exact source RX virtual text bytes and discarded pristine timestamps.
The full tier permits nonidentity mappings, including the high trampoline VA.
No translation success, physical replacement or new camera is assumed. -/
namespace Xv6.Kernel.KernelTextDatum
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := KernelDatum.Capacity
abbrev Tier := KernelDatum.Tier
abbrev vpn := KernelDatum.vpn
abbrev physical := KernelDatum.physical

def textEnd : Nat := 0x80007000
/-- The physical trampoline page is already inside this source interval. -/
def AddrIsText (pa : PhysicalAddress) : Prop :=
  0x80000000 ≤ pa.toNat ∧ pa.toNat < textEnd

def SamePage (va : BitVec 64) (n : Nat) : Prop := va.toNat % 4096 + n ≤ 4096

def lowHalf (word : BitVec 32) : BitVec 16 := word.extractLsb' 0 16
def highHalf (word : BitVec 32) : BitVec 16 := word.extractLsb' 16 16

variable {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)

abbrev rawByte (pa : PhysicalAddress) (dq : DFrac) (value : Byte) : IProp GF :=
  Heap.pointsto capacity.machine.era.heap ⟨era.heap, era.metadata⟩ pa dq value
abbrev pristine (pa : PhysicalAddress) : IProp GF :=
  TsoRead.pristineByte capacity.machine.era.heap.ledger era.timestamps pa

def claim (tier : Tier) (va : BitVec 64) (ppn : PtTree.PPN) : IProp GF :=
  iprop(KptGhost.mapAt capacity.ghost era.kernelMap (vpn va) ppn .rx ∗
    ⌜KernelDatum.Positive va ∧ AddrIsText (physical ppn va) ∧ KernelDatum.Pin tier ppn va⌝)

def byte (tier : Tier) (va : BitVec 64) (dq : DFrac) (value : Byte) : IProp GF :=
  iprop(∃ ppn, claim capacity era tier va ppn ∗ rawByte capacity era (physical ppn va) dq value ∗
    pristine capacity era (physical ppn va))

/-- No alignment or same-page condition is hidden in the virtual window.
A four-byte window at page offset4094 retains both pages' mapping claims. -/
def window (tier : Tier) (va : BitVec 64) (n : Nat) (dq : DFrac)
    (word : BitVec (8 * n)) : IProp GF :=
  iprop([∗list] j ∈ List.range n, byte capacity era tier (addressAdd va j) dq (nthByte word j))

def claims (tier : Tier) (va : BitVec 64) (n : Nat) (ppn : PtTree.PPN) : IProp GF :=
  iprop([∗list] j ∈ List.range n, claim capacity era tier (addressAdd va j) ppn)

abbrev physicalWindow (pa : PhysicalAddress) (n : Nat) (dq : DFrac)
    (word : BitVec (8 * n)) : IProp GF :=
  TsoRead.byteWindow capacity.machine.era.heap.ledger era.heap pa n dq word
abbrev pristineWindow (pa : PhysicalAddress) (n : Nat) : IProp GF :=
  TsoRead.pristineWindow capacity.machine.era.heap.ledger era.timestamps pa n
abbrev contextWindow (ξ : TsoContext.CtxId) (pa : PhysicalAddress) (n : Nat)
    (word : BitVec (8 * n)) : IProp GF :=
  TsoContextBytes.window (TsoContextReadWP.contextCapacity capacity.machine)
    (TsoContextReadWP.contextNames era) ξ pa n .discard word
abbrev heapAt (g : State) : IProp GF := Era.heapInterpAt capacity.machine.era era g
abbrev tsoAt (g : State) : IProp GF :=
  Tso.Interp.tsoInterpAt capacity.machine.era.tso era.tsoNames era.imageBytes g

end Xv6.Kernel.KernelTextDatum
