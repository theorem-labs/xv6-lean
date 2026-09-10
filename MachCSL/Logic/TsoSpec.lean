import MachCSL.Logic.TsoPredicates

/-! The first TSO ledger contract, independent of its proof implementation.
This is a proposition-valued record of actual native Iris entailments.
It neither replaces ownership with Lean conjunctions nor assumes a machine WP.
-/
namespace MachCSL.Logic.Tso
open MachCSL.Memory Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

structure LedgerSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  alloc : ∀ (memory : AddressMap Byte) (timestamps : AddressMap TimestampElem),
    iprop(⊢ |==> ∃ names : Names,
      byteAuth capacity names.bytes (.own 1) memory ∗
      timestampAuth capacity names.timestamps (.own 1) timestamps ∗
      ([∗map] a ↦ byte ∈ memory, byteElem capacity names.bytes (.own 1) a byte) ∗
      ([∗map] a ↦ e ∈ timestamps, timestampElem capacity names.timestamps (.own 1) a e))
  pin_agree : ∀ names a dq1 dq2 byte1 byte2 t1 t2 bound1 bound2 allowed1 allowed2,
    iprop(physLedgerPin capacity names a dq1 byte1 t1 bound1 allowed1 ∗
      physLedgerPin capacity names a dq2 byte2 t2 bound2 allowed2 ⊢
      ⌜byte1 = byte2 ∧ t1 = t2 ∧ bound1 = bound2 ∧ allowed1 = allowed2⌝)
  pin_read : ∀ names a dq byte t bound allowed image memory log timestamps,
    TimestampMapOK image memory log timestamps → ∀ h view, bound ≤ view →
    iprop(⊢ timestampAuth capacity names.timestamps (.own 1) timestamps -∗
      physLedgerPin capacity names a dq byte t bound allowed -∗
      ⌜∃ b, read image log h view a = some b ∧ b ∈ allowed⌝)
  window_valid : ∀ names a dq byte t window image memory log timestamps,
    TimestampMapOK image memory log timestamps →
    iprop(⊢ timestampAuth capacity names.timestamps (.own 1) timestamps -∗
      physLedgerWpay capacity names a dq byte t window -∗ ⌜WindowOK image log a window⌝)

end MachCSL.Logic.Tso
