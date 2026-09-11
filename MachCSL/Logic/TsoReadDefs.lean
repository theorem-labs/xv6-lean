import MachCSL.Logic.EraStateDefs
import MachCSL.Memory.ReadBytes

namespace MachCSL.Logic.TsoRead
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

/-- Actual plain-read writeback: only this CPU's view changes. -/
def advanceView (g : State) (cpu : CPU) (view : Nat) : State :=
  { g with views := updateHart g.views cpu view }

/-- Source `RiscvPtsto.pristine_elem`: discarded timestamp zero, no payload. -/
def pristineByte {GF : BundledGFunctors} (capacity : Tso.Capacity GF)
    (γ : GName) (a : PhysicalAddress) : IProp GF :=
  Tso.timestampElem capacity γ .discard a (0, Tso.payNone)

def pristineWindow {GF : BundledGFunctors} (capacity : Tso.Capacity GF)
    (γ : GName) (a : PhysicalAddress) (n : Nat) : IProp GF :=
  iprop([∗list] j ∈ List.range n, pristineByte capacity γ (addressAdd a j))

/-- Physical byte cells use the same modular address list as the actual request. -/
def byteWindow {GF : BundledGFunctors} (capacity : Tso.Capacity GF)
    (γ : GName) (a : PhysicalAddress) (n : Nat) (dq : DFrac) (word : BitVec (8 * n)) : IProp GF :=
  iprop([∗list] j ∈ List.range n,
    Tso.physBytePointsto capacity γ (addressAdd a j) dq (nthByte word j))

/-- Full timestamp-zero clients may be irreversibly made pristine. -/
def initialTimestampWindow {GF : BundledGFunctors} (capacity : Tso.Capacity GF)
    (γ : GName) (a : PhysicalAddress) (n : Nat) : IProp GF :=
  iprop([∗list] j ∈ List.range n,
    Tso.timestampElem capacity γ (.own 1) (addressAdd a j) (0, Tso.payNone))

end MachCSL.Logic.TsoRead
