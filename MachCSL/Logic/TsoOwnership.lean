import MachCSL.Logic.TsoSpec

/-! Proofs of the native TSO ledger contract. Public predicates and the contract
are importable independently of this implementation. -/
namespace MachCSL.Logic.Tso
open MachCSL.Memory Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance byteElem_timeless γ dq a byte : Timeless (byteElem capacity γ dq a byte) := by
  letI := capacity.bytes
  unfold byteElem
  infer_instance

instance timestampElem_timeless γ dq a e : Timeless (timestampElem capacity γ dq a e) := by
  letI := capacity.timestamps
  unfold timestampElem
  infer_instance

instance physBytePointsto_timeless γ a dq byte :
    Timeless (physBytePointsto capacity γ a dq byte) := by
  unfold physBytePointsto
  infer_instance

instance physLedgerPin_timeless names a dq byte t bound allowed :
    Timeless (physLedgerPin capacity names a dq byte t bound allowed) := by
  unfold physLedgerPin
  infer_instance

instance physLedgerWpay_timeless names a dq byte t window :
    Timeless (physLedgerWpay capacity names a dq byte t window) := by
  unfold physLedgerWpay
  infer_instance

instance physBytePointsto_fractional γ a byte :
    Fractional (fun q => physBytePointsto capacity γ a (.own q) byte) := by
  letI := capacity.bytes
  infer_instance

instance physLedgerPin_fractional names a byte t bound allowed :
    Fractional (fun q => physLedgerPin capacity names a (.own q) byte t bound allowed) := by
  letI := capacity.bytes
  letI := capacity.timestamps
  infer_instance

instance physLedgerWpay_fractional names a byte t window :
    Fractional (fun q => physLedgerWpay capacity names a (.own q) byte t window) := by
  letI := capacity.bytes
  letI := capacity.timestamps
  infer_instance

theorem physLedgerPin_split names a byte t bound allowed (q1 q2 : Qp) :
    iprop(physLedgerPin capacity names a (.own (q1 + q2)) byte t bound allowed ⊣⊢
      physLedgerPin capacity names a (.own q1) byte t bound allowed ∗
      physLedgerPin capacity names a (.own q2) byte t bound allowed) :=
  Fractional.fractional (Φ := fun q => physLedgerPin capacity names a (.own q) byte t bound allowed) q1 q2

theorem physLedgerWpay_split names a byte t window (q1 q2 : Qp) :
    iprop(physLedgerWpay capacity names a (.own (q1 + q2)) byte t window ⊣⊢
      physLedgerWpay capacity names a (.own q1) byte t window ∗
      physLedgerWpay capacity names a (.own q2) byte t window) :=
  Fractional.fractional (Φ := fun q => physLedgerWpay capacity names a (.own q) byte t window) q1 q2

theorem physBytePointsto_ram γ a dq byte :
    iprop(physBytePointsto capacity γ a dq byte ⊢ ⌜AddrIsRAM a⌝) := by
  iintro ⟨_, H⟩
  iexact H

theorem physLedgerPin_forget names a dq byte t bound allowed :
    iprop(physLedgerPin capacity names a dq byte t bound allowed ⊢
      physBytePointsto capacity names.bytes a dq byte) := by
  iintro ⟨H, _⟩
  iexact H

theorem physLedgerPin_ram names a dq byte t bound allowed :
    iprop(physLedgerPin capacity names a dq byte t bound allowed ⊢ ⌜AddrIsRAM a⌝) := by
  iintro ⟨⟨_, H⟩, _⟩
  iexact H

theorem physLedgerWpay_forget names a dq byte t window :
    iprop(physLedgerWpay capacity names a dq byte t window ⊢
      physBytePointsto capacity names.bytes a dq byte) := by
  iintro ⟨H, _⟩
  iexact H

theorem physBytePointsto_agree γ a dq1 dq2 byte1 byte2 :
    iprop(physBytePointsto capacity γ a dq1 byte1 ∗
      physBytePointsto capacity γ a dq2 byte2 ⊢ ⌜byte1 = byte2⌝) := by
  letI := capacity.bytes
  iintro ⟨⟨H1, _⟩, ⟨H2, _⟩⟩
  iapply ghost_map_elem_agree $$ [$H1 $H2]

theorem physLedgerPin_agree names a dq1 dq2 byte1 byte2 t1 t2 bound1 bound2 allowed1 allowed2 :
    iprop(physLedgerPin capacity names a dq1 byte1 t1 bound1 allowed1 ∗
      physLedgerPin capacity names a dq2 byte2 t2 bound2 allowed2 ⊢
      ⌜byte1 = byte2 ∧ t1 = t2 ∧ bound1 = bound2 ∧ allowed1 = allowed2⌝) := by
  letI := capacity.timestamps
  iintro ⟨⟨H1, T1⟩, ⟨H2, T2⟩⟩
  ihave %hb := physBytePointsto_agree capacity names.bytes a dq1 dq2 byte1 byte2 $$ [$H1 $H2]
  ihave %ht := ghost_map_elem_agree names.timestamps a dq1 dq2
    (t1, payPin allowed1 bound1) (t2, payPin allowed2 bound2) $$ [$T1 $T2]
  ipureintro
  have ht' := congrArg (fun e : TimestampElem => e.2.pin) ht
  simp only [payPin, Option.some.injEq, Prod.mk.injEq] at ht'
  exact ⟨hb, congrArg Prod.fst ht, ht'.2, ht'.1⟩

theorem physLedgerWpay_agree names a dq1 dq2 byte1 byte2 t1 t2 window1 window2 :
    iprop(physLedgerWpay capacity names a dq1 byte1 t1 window1 ∗
      physLedgerWpay capacity names a dq2 byte2 t2 window2 ⊢
      ⌜byte1 = byte2 ∧ t1 = t2 ∧ window1 = window2⌝) := by
  letI := capacity.timestamps
  iintro ⟨⟨H1, T1⟩, ⟨H2, T2⟩⟩
  ihave %hb := physBytePointsto_agree capacity names.bytes a dq1 dq2 byte1 byte2 $$ [$H1 $H2]
  ihave %ht := ghost_map_elem_agree names.timestamps a dq1 dq2
    (t1, payWin window1) (t2, payWin window2) $$ [$T1 $T2]
  ipureintro
  have hw := congrArg (fun e : TimestampElem => e.2.win) ht
  exact ⟨hb, congrArg Prod.fst ht, Option.some.inj hw⟩

theorem physLedgerPin_ne names a1 a2 dq byte1 byte2 t1 t2 bound1 bound2 allowed1 allowed2 :
    iprop(⊢ physLedgerPin capacity names a1 (.own 1) byte1 t1 bound1 allowed1 -∗
      physLedgerPin capacity names a2 dq byte2 t2 bound2 allowed2 -∗ ⌜a1 ≠ a2⌝) := by
  letI := capacity.bytes
  iintro ⟨⟨H1, _⟩, _⟩ ⟨⟨H2, _⟩, _⟩
  iapply ghost_map_elem_ne $$ H1 H2

theorem timestamp_lookup γ dq timestamps a dq' e :
    iprop(⊢ timestampAuth capacity γ dq timestamps -∗
      timestampElem capacity γ dq' a e -∗ ⌜timestamps[a]? = some e⌝) := by
  letI := capacity.timestamps
  exact ghost_map_lookup

theorem timestamp_update γ timestamps a e (replacement : TimestampElem) :
    iprop(⊢ timestampAuth capacity γ (.own 1) timestamps -∗
      timestampElem capacity γ (.own 1) a e ==∗
      timestampAuth capacity γ (.own 1) (Iris.Std.PartialMap.insert timestamps a replacement) ∗
      timestampElem capacity γ (.own 1) a replacement) := by
  letI := capacity.timestamps
  exact ghost_map_update (GF := GF) (K := PhysicalAddress) (H := AddressMap)
    (γ := γ) (m := timestamps) (k := a) (v := e) replacement

/-- Allocate actual authorities and full element ownership for both maps.
    This does not assert that the caller's maps satisfy TimestampMapOK. -/
theorem ledger_alloc (memory : AddressMap Byte) (timestamps : AddressMap TimestampElem) :
    iprop(⊢ |==> ∃ names : Names,
      byteAuth capacity names.bytes (.own 1) memory ∗
      timestampAuth capacity names.timestamps (.own 1) timestamps ∗
      ([∗map] a ↦ byte ∈ memory, byteElem capacity names.bytes (.own 1) a byte) ∗
      ([∗map] a ↦ e ∈ timestamps, timestampElem capacity names.timestamps (.own 1) a e)) := by
  letI := capacity.bytes
  letI := capacity.timestamps
  imod ghost_map_alloc memory with ⟨%γb, Hb, Hbe⟩
  imod ghost_map_alloc timestamps with ⟨%γt, Ht, Hte⟩
  imodintro
  iexists (Names.mk γb γt)
  iframe

/-- The source window interpretation is recovered from its actual authoritative entry. -/
theorem physLedgerWpay_valid (names : Names) (a : PhysicalAddress) (dq : DFrac)
    (byte : Byte) (t : Nat) (window : Window)
    (image memory : ByteMap 64) (log : WriteLog 64) (timestamps : AddressMap TimestampElem)
    (tie : TimestampMapOK image memory log timestamps) :
    iprop(⊢ timestampAuth capacity names.timestamps (.own 1) timestamps -∗
      physLedgerWpay capacity names a dq byte t window -∗ ⌜WindowOK image log a window⌝) := by
  iintro Hauth ⟨_, Helem⟩
  ihave %lookup := timestamp_lookup capacity names.timestamps (.own 1) timestamps a dq
    (t, payWin window) $$ Hauth Helem
  ipureintro
  exact timestampOK_win (tie a _ lookup) rfl

/-- Owning the pin alone is insufficient: this consumes the real timestamp
    authority and the source's semantic tie to derive the read consequence. -/
theorem physLedgerPin_read (names : Names) (a : PhysicalAddress) (dq : DFrac)
    (byte : Byte) (t bound : Nat) (allowed : ByteSet)
    (image memory : ByteMap 64) (log : WriteLog 64) (timestamps : AddressMap TimestampElem)
    (tie : TimestampMapOK image memory log timestamps) (h : Agent) (view : Nat)
    (above : bound ≤ view) :
    iprop(⊢ timestampAuth capacity names.timestamps (.own 1) timestamps -∗
      physLedgerPin capacity names a dq byte t bound allowed -∗
      ⌜∃ b, read image log h view a = some b ∧ b ∈ allowed⌝) := by
  iintro Hauth ⟨_, Helem⟩
  ihave %lookup := timestamp_lookup capacity names.timestamps (.own 1) timestamps a dq
    (t, payPin allowed bound) $$ Hauth Helem
  ipureintro
  exact timestampOK_pin (tie a _ lookup) rfl h view above

/-- Link the independent contract to this implementation, with the same explicit capacity. -/
theorem ledgerSpec : LedgerSpec capacity :=
  ⟨ledger_alloc capacity, physLedgerPin_agree capacity, physLedgerPin_read capacity,
    physLedgerWpay_valid capacity⟩

/-- The registry discharges functor capacity. Runtime allocation and the machine
    state tie remain the explicit updates/premises in this contract. -/
theorem registryLedgerSpec : LedgerSpec registryCapacity := ledgerSpec registryCapacity

end MachCSL.Logic.Tso
