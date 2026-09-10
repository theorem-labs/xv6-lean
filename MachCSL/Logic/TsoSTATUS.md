# TSO ledger ownership: first native Iris resource layer

This is a partial port of the paper's memory ghost resources. It uses the real
native Iris `IProp`, `HeapView`, `Agree`, `DiscreteO`, `DFrac`, authoritative
ownership, and frame-preserving updates. It does not establish the machine
state interpretation, a machine-code WP, or whole-system adequacy.

The source is mit-pdos/xv6iris `arxiv-v1`, commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The native Iris dependency is
`728a17140939e49af9236f7cb0d037da9ec52435`, using Lean 4.32.2.

## Files and contract boundary

- `TsoDefs.lean`: all four timestamp payload data types, their exact pure
  interpretation predicates, the byte pin lifecycle, and interpretation
  projections. This includes the full release-history and word-set-predicate
  payloads even though their ownership lifecycle proofs are still pending.
- `TsoGhost.lean`: a two-entry partial functor registry, explicit slot
  certificates, generic capacity data, runtime names, authoritative/element
  ownership aliases, and the pointwise `TimestampMapOK` interpretation.
- `TsoPredicates.lean`: `physBytePointsto`, `physLedgerPin`, `physLedgerWpay`,
  `pinMapOwn`, and `wpayMapOwn`, all actual native Iris propositions.
- `TsoSpec.lean`: the independent proposition-valued `LedgerSpec` contract,
  containing allocation, pin agreement/read, and window interpretation claims.
  It imports the predicates, not their ownership proof implementation.
- `TsoOwnership.lean`: ownership laws and `ledgerSpec`, the proof constructor
  for that contract. `registryLedgerSpec` supplies the concrete registry's
  capacity; runtime allocation and the semantic interpretation remain explicit.

## Source mapping

| Paper source | Lean declaration |
|---|---|
| `TsoMemPa.byteset` | `ByteSet` (`Std.ExtTreeSet (BitVec 8)`) |
| `TsoMemPa.ts_win`, `ts_rel`, `ts_pinw`, `ts_pay` | `Window`, `Release`, `WordPin`, `Payload` |
| `ts_pay_none/pin/win/rel/pinw`, `ts_elem` | `payNone/Pin/Win/Rel/Pinw`, `TimestampElem` |
| `pin_ok`, `own_last_fl`, `win_ok1`, `rel_ok1`, `pinw_ok1`, `ts_ok` | `PinOK`, `OwnLastFloor`, `WindowOK`, `ReleaseOK`, `WordPinOK`, `TimestampOK` |
| `pin_ok_mint/app/app_frame/mono`, `read_down_app_frame` | `pinOK_mint/append/append_frame/mono`, `readDown_append_frame` |
| `ts_ok_latest/pin/win/rel/pinw/unpinned` | `timestampOK_latest/pin/win/rel/pinw/unpinned` |
| `TsoGhost.tsomem_tsG` | `Capacity.timestamps`, `timestampSlot`, `TimestampRA` |
| `gen_heap` value-map component used by `RiscvPtsto.phys_pointsto` | `Capacity.bytes`, `byteSlot`, `ByteRA` |
| `RiscvPtsto.addr_is_ram` (lines 1050–1082) | `AddrIsRAM`, the exact unsigned interval `[0x80000000, 0x88000000)` |
| `RiscvPtsto.phys_pointsto` (line 1551) | `physBytePointsto` (value ownership and RAM fact) |
| `TsoCtx.phys_ledger_pin/wpay` (lines 2686–2731) | `physLedgerPin`, `physLedgerWpay` |
| `TsoCtx.pin_map_own/wpay_map_own` (lines 2718–2745) | `pinMapOwn`, `wpayMapOwn` |

The interpretation data comes from `TsoMemPa.v:1740–1798, 2115–2152,
2553–2579, 2696–2753`; the byte pin lifecycle is at lines 591–651.
The declarations retain every source payload arm and its implications. Window
floors, per-agent own-last indices, release histories, and the arbitrary
predicate on whole words remain explicit. A word-set pin is not weakened to
independent allowed-byte sets. Addresses retain the 64-bit carrier and modular
`addressAdd`. Source `is_Some` is expressed by `Option.isSome = true`.

## Resource registry and ownership laws

Slot 0 stores the physical byte map, with resource algebra
`HeapView PhysicalAddress (Agree (DiscreteO Byte)) AddressMap`. Slot 1 stores
timestamps and all payloads using the same construction over `TimestampElem`.
`AddressMap` is `Std.ExtTreeMap (BitVec 64)`. The slot-index injection and the
fact that indices at least 2 remain the default unit functor are proved.
Each ownership alias passes its intended `GhostMapG` certificate explicitly
through its capacity argument. Runtime ghost names are separate data; equal
numerical names in different slots do not alias resources.

The physical slot is exactly the value-map component of native `gen_heap`.
It does **not** claim to supply the two metadata resources of full `gen_heap`.
Likewise, the registry does **not** yet supply the other source `tsoMemΣ`
resources: log-entry map, per-agent view authority, and dirty monotone set.
The shared mono-nat slot also remains to be allocated once in the full registry.
These are missing capabilities to add, not assumed instances.

The checked ownership exports include timelessness; arbitrary positive fraction
splitting for both pinned and window cells; forgetting to physical byte
ownership; RAM extraction; byte, timestamp, bound, set and full-window
agreement; full-fraction pinned-cell exclusivity; authoritative timestamp
lookup; full-authority/full-element timestamp update; and allocation of both
actual maps with full element ownership. Allocation does not assert that the
chosen maps satisfy any machine interpretation.

`physLedgerPin_read` requires `TimestampMapOK`, actual authoritative ownership
of that timestamp map, and the pin fragment. It concludes the exact allowed-set
read property at a view at least the pin bound. `physLedgerWpay_valid` similarly
recovers the full `WindowOK` predicate from the authority and window fragment.
The source interpretation is an explicit premise until the machine state
interpretation is constructed and preserved. The naked pin or window token
alone never asserts a fact about current machine memory.

## Validation and next obligations

`python3 tools/lake.py build MachCSL.Logic.TsoOwnership` passed (212 jobs).
All 38 named theorem/instance exports and `registryCapacity` were checked with
`#print axioms`; only standard `propext`, `Classical.choice`, and `Quot.sound`
appeared. There are no `sorry`, custom axioms, or native decision axioms.
The exported types of allocation and the pin read rule were inspected to ensure
that capacity, runtime names, and the semantic tie are visible.

The byte-pin pure lifecycle is complete. Window/release/word-set preservation
and read theorems, full gen_heap metadata, source TSO view/log/dirty resources,
era allocation, context ownership, and machine state interpretation still need
to be ported. This implementation does not mechanically translate Rocq terms;
cross-prover definition correspondence remains distinct from these Lean proofs.
No whole-system or closed machine-code acceptance gate is discharged here.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
