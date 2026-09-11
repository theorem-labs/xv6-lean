import MachCSL.Logic.TsoInterpDefs
import MachCSL.Logic.TsoPredicates

/-! Context-free publication credentials, `CtxValues.v:295–300,375–395,426–486`.
All assertions use the existing physical byte, timestamp, history and view
capacities. No page-table invariant, current context, or new camera is assumed. -/
namespace MachCSL.Logic.TsoPinnedRead
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

abbrev Capacity := Tso.Interp.Capacity
abbrev Names := Tso.Interp.EraNames

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- A persistent receipt of an actual byte-writing message authored by `h`.
Positions are one-based; native log ownership uses the zero-based index. -/
def ownAnchor (names : Names) (h : Agent) (a : PhysicalAddress) (position : Nat) : IProp GF :=
  iprop(∃ (index : Nat) (msg : Message 64) (byte : Byte),
    ⌜position = index + 1⌝ ∗
    Tso.History.logElem capacity.history names.logEntries index msg ∗
    ⌜msgByte msg a = some byte ∧ msg.author = h⌝)

/-- Source `cv_boot_cred`: the boot hart can use its own publication receipt
without advancing its actual view to the publication bound. -/
def bootCredential (names : Names) (cpu : CPU) (bound : Nat) : IProp GF :=
  iprop(Tso.Views.viewLB capacity.views names.views names.logLength (hartAgent cpu) bound ∨
    (⌜hartAgent cpu = 0⌝ ∗ Tso.Views.llb capacity.views names.logLength bound))

/-- The three exact publication-anchor alternatives at one slot byte. -/
def slotAnchor (names : Names) (a : PhysicalAddress) (floor : Nat) : IProp GF :=
  iprop(⌜floor = 0⌝ ∨ ownAnchor capacity names 0 a floor ∨
    Tso.Views.viewLB capacity.views names.views names.logLength 0 floor)

/-- Source per-byte floors, preserving arbitrary fractions and modular addresses.
The `value` function avoids default or out-of-bounds list accesses. -/
def slotBytes (names : Names) (a : PhysicalAddress) (n : Nat) (dq : DFrac)
    (value : Nat → Byte) (bound : Nat) (sets : Nat → Tso.ByteSet) : IProp GF :=
  iprop([∗list] j ∈ List.range n, ∃ (floor time : Nat),
    ⌜floor ≤ bound⌝ ∗
    Tso.physLedgerPin capacity.ledger names.ledger (addressAdd a j) dq (value j)
      time floor (sets j) ∗ slotAnchor capacity names (addressAdd a j) floor)

def slotWord (names : Names) (a : PhysicalAddress) (dq : DFrac)
    (word : BitVec 64) (bound : Nat) (sets : Nat → Tso.ByteSet) : IProp GF :=
  slotBytes capacity names a 8 dq (nthByte word) bound sets

/-- The per-byte all-view statement; it does not equate an observed leaf with
the currently owned physical word. Canonical PTE assembly is a later layer. -/
def SlotReads (g : State) (cpu : CPU) (a : PhysicalAddress) (n : Nat)
    (sets : Nat → Tso.ByteSet) : Prop :=
  ∀ view, g.views cpu ≤ view → ∀ j, j < n → ∃ byte,
    read g.image g.log (hartAgent cpu) view (addressAdd a j) = some byte ∧ byte ∈ sets j

end MachCSL.Logic.TsoPinnedRead
