import MachCSL.Logic.TsoHistoryDefs
import MachCSL.Memory.FiniteMap
import MachCSL.Machine.Boot

/-! The actual machine-state TSO interpretation from `RiscvPtsto.v:2099–2141`.
This is one era conjunct, not the full machine interpretation or gen_heap. -/
namespace MachCSL.Logic.Tso.Interp
open MachCSL.Memory MachCSL.Machine Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

structure Capacity (GF : BundledGFunctors) where
  ledger : Tso.Capacity GF
  views : Views.Capacity GF
  history : History.Capacity GF

def registryCapacity : Capacity History.registry :=
  ⟨History.ledgerCapacity, History.viewsCapacity, History.registryCapacity⟩

/-- Runtime names are allocated separately from functor capacity. -/
structure EraNames where
  ledger : Tso.Names
  logEntries : GName
  logLength : GName
  views : GName

/-- Every Nat agent is covered: CPU views below eight; log length otherwise. -/
def avf (g : State) (h : Agent) : Nat :=
  if bound : h < 8 then g.views ⟨h, bound⟩ else g.log.length

/-- Pointwise domain equality is the extensional form of source `dom TM = dom mem`. -/
def TimestampDomain (timestamps : AddressMap TimestampElem) (memory : ByteMap 64) : Prop :=
  ∀ a, timestamps[a]?.isSome ↔ Domain memory a

/-- The exact source boot timestamps, preserving every present byte's key. -/
def bootTimestamps (memory : AddressMap Byte) : AddressMap TimestampElem :=
  memory.map (fun _ _ => (0, payNone))

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def tsoInterpAt (names : EraNames) (eraImage : ByteMap 64) (g : State) : IProp GF :=
  iprop(∃ (timestamps : AddressMap TimestampElem) (entries : History.LogMap (Message 64)),
    timestampAuth capacity.ledger names.ledger.timestamps (.own 1) timestamps ∗
    ⌜TimestampDomain timestamps g.memory⌝ ∗
    ⌜TimestampMapOK g.image g.memory g.log timestamps⌝ ∗
    History.logAuth capacity.history names.logEntries (.own 1) entries ∗
    ⌜History.LogRep entries g.log⌝ ∗
    Views.natAuth capacity.views names.logLength (.own 1) g.log.length ∗
    Views.viewAuth capacity.views names.views (avf g) ∗
    ⌜MemoryOK g ∧ g.image = eraImage⌝)

/-- The separate gen_heap value-map component and its exact machine-memory tie.
The gen_heap metadata slots are deliberately not represented by this name. -/
def byteInterpAt (names : EraNames) (memory : AddressMap Byte) (g : State) : IProp GF :=
  iprop(byteAuth capacity.ledger names.ledger.bytes (.own 1) memory ∗
    ⌜FiniteMap.decode memory = g.memory⌝)

/-- Full client fragments at birth; writable memory is not made read-only. -/
def bootClients (names : EraNames) (memory : AddressMap Byte) : IProp GF :=
  iprop(([∗map] a ↦ byte ∈ memory,
      byteElem capacity.ledger names.ledger.bytes (.own 1) a byte) ∗
    ([∗map] a ↦ e ∈ bootTimestamps memory,
      timestampElem capacity.ledger names.ledger.timestamps (.own 1) a e) ∗
    Views.natLB capacity.views names.logLength 0)

end MachCSL.Logic.Tso.Interp
