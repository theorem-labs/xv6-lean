import MachCSL.Logic.TsoGhost

/-!
Native Iris ownership for the byte/timestamp component of the source physical
ledger (`RiscvPtsto.phys_pointsto`; `TsoCtx.phys_ledger_pin/phys_ledger_wpay`).
`physBytePointsto` names the gen_heap byte component explicitly: no gen_heap
metadata token or full machine interpretation is claimed by this module.
-/
namespace MachCSL.Logic.Tso
open MachCSL.Memory Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Exactly the gen_heap value fragment and source RAM condition. -/
abbrev physBytePointsto (γ : GName) (a : PhysicalAddress) (dq : DFrac) (byte : Byte) : IProp GF :=
  iprop(byteElem capacity γ dq a byte ∗ ⌜AddrIsRAM a⌝)

abbrev physLedgerPin (names : Names) (a : PhysicalAddress) (dq : DFrac) (byte : Byte)
    (t bound : Nat) (allowed : ByteSet) : IProp GF :=
  iprop(physBytePointsto capacity names.bytes a dq byte ∗
    timestampElem capacity names.timestamps dq a (t, payPin allowed bound))

abbrev physLedgerWpay (names : Names) (a : PhysicalAddress) (dq : DFrac) (byte : Byte)
    (t : Nat) (window : Window) : IProp GF :=
  iprop(physBytePointsto capacity names.bytes a dq byte ∗
    timestampElem capacity names.timestamps dq a (t, payWin window))

/-- Source `pin_map_own`: one separately owned pinned ledger cell per map entry. -/
abbrev pinMapOwn (names : Names) (memory : AddressMap Byte) (dq : DFrac)
    (bounds : PhysicalAddress → Nat) (sets : PhysicalAddress → ByteSet) : IProp GF :=
  iprop([∗map] a ↦ byte ∈ memory, ∃ t : Nat,
    physLedgerPin capacity names a dq byte t (bounds a) (sets a))

/-- Source `wpay_map_own`; each address retains its own full window descriptor. -/
abbrev wpayMapOwn (names : Names) (memory : AddressMap Byte) (dq : DFrac)
    (windows : PhysicalAddress → Window) : IProp GF :=
  iprop([∗map] a ↦ byte ∈ memory, ∃ t : Nat,
    physLedgerWpay capacity names a dq byte t (windows a))

end MachCSL.Logic.Tso
