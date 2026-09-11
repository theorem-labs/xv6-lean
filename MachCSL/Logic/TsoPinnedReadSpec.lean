import MachCSL.Logic.TsoPinnedReadDefs

namespace MachCSL.Logic.TsoPinnedRead
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

structure ReadSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  pinValid : ∀ names image g a dq byte time bound allowed,
    iprop(⊢ Tso.Interp.tsoInterpAt capacity names image g -∗
      Tso.physLedgerPin capacity.ledger names.ledger a dq byte time bound allowed -∗
      ⌜Tso.PinOK g.image g.log a bound allowed⌝)
  authorRead : ∀ names image g h a dq byte time bound allowed position,
    bound ≤ position →
    iprop(⊢ Tso.Interp.tsoInterpAt capacity names image g -∗
      Tso.physLedgerPin capacity.ledger names.ledger a dq byte time bound allowed -∗
      ownAnchor capacity names h a position -∗
      ⌜∀ view, ∃ v, read g.image g.log h view a = some v ∧ v ∈ allowed⌝)
  slotRead : ∀ names image g cpu a n dq value bound sets,
    iprop(⊢ Tso.Interp.tsoInterpAt capacity names image g -∗
      bootCredential capacity names cpu bound -∗
      slotBytes capacity names a n dq value bound sets -∗
      ⌜SlotReads g cpu a n sets⌝)
  slotReadPreserve : ∀ names image g cpu a n dq value bound sets,
    iprop(⊢ Tso.Interp.tsoInterpAt capacity names image g -∗
      bootCredential capacity names cpu bound -∗
      slotBytes capacity names a n dq value bound sets -∗
      Tso.Interp.tsoInterpAt capacity names image g ∗
      bootCredential capacity names cpu bound ∗ slotBytes capacity names a n dq value bound sets ∗
      ⌜SlotReads g cpu a n sets⌝)

end MachCSL.Logic.TsoPinnedRead
