import MachCSL.Logic.TsoInterpDefs

namespace MachCSL.Logic.Tso.Interp
open MachCSL.Memory MachCSL.Machine Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

/-- Independent contract for the source TSO era conjunct and birth allocation. -/
structure InterpSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  image : ∀ names eraImage g,
    iprop(⊢ tsoInterpAt capacity names eraImage g -∗ ⌜g.image = eraImage⌝)
  memoryOK : ∀ names eraImage g,
    iprop(⊢ tsoInterpAt capacity names eraImage g -∗ ⌜MemoryOK g⌝)
  timestampValid : ∀ names eraImage g a dq e,
    iprop(⊢ tsoInterpAt capacity names eraImage g -∗
      timestampElem capacity.ledger names.ledger.timestamps dq a e -∗
      ⌜TimestampOK g.image g.memory g.log a e⌝)
  allocate : ∀ (image : BootImage) (g : State) (memory : AddressMap Byte),
    BootFacts image g → FiniteMap.decode memory = g.memory →
    iprop(⊢ |==> ∃ names : EraNames,
      tsoInterpAt capacity names g.image g ∗
      byteInterpAt capacity names memory g ∗ bootClients capacity names memory)

end MachCSL.Logic.Tso.Interp
