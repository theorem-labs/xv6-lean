# Native RX text bytes and pristine physical windows

This is the implemented `Xv6.Kernel.KernelTextDatum` boundary. The source is
xv6iris arxiv-v1 `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
The coordinator approved all 36 contract fields before implementation.
All now have kernel-checked native proofs and concrete registry links.

## Source mapping

| Source | Native interface |
|---|---|
| RiscvPtsto1070–1120 | `textEnd`, `AddrIsText`, RAM projection and checked linker-symbol/trampoline arithmetic. |
| RiscvPtsto1180–1228 | Reuse existing `KernelDatum.Tier`, `Pin`, VPN and physical-address reconstruction. |
| RiscvPtsto1505–1523 | `pristine`, `claim`, `byte`: RX mapping, positive virtual address, physical text membership, tier pin, actual byte ownership and discarded timestamp `(0,None)`. |
| RiscvPtsto2480–2608,2730–2748 | Access/close at the same byte, mapping agreement, validity, persistence, tier weakening and given-PPN access. |
| KernelText64 and its window extraction rules | Virtual `window` is a list of exact per-byte text ownership; it does not silently default absent code bytes. Full source code-map ownership is a later producer. |
| InstrBytes53–73,196–225,281–497 | Two/four-byte windows, exact low/high halves, page-local physical extraction and unrestricted four-to-two-plus-two splitting. |
| HartLift2, text_byte_phys_pristine456 and text_tso_read_bytes468 | Identity physical extraction and every-agent/every-view immutable readback from actual heap/TSO authorities. |
| BootCarve184–211 and KMap217–233 | Closing text ownership requires supplied pristine resources and RX claims. This prefix does not mint them from physical bytes. |

`AddrIsText` is exactly the physical interval `[0x80000000,0x80007000)`.
The physical trampoline page `[0x80006000,0x80007000)` is already included.
There is no extra disjunction or inferred high-VA text interval. The full tier
permits nonidentity mappings, including the high trampoline virtual address.

## Contracts and resource identity

`PureSpec` has nine fields: text-in-RAM, exact etext symbol, trampoline-page
membership, two/four-alignment page bounds, same-page VPN and physical-offset
laws, and low/high byte extraction. `Spec` has eighteen fields: eight native
persistence/timelessness facts and ten access, claim, agreement, validity,
weakening and persistence rules. `WindowSpec` has nine fields: extraction,
closing, first claim, identity extraction, four-byte splitting, two discarded
context conversions, and two immutable readback rules.

Capacity is the existing `KernelDatum.Capacity`. Mapping ownership uses the
same era's `kernelMap`; raw bytes use its existing heap and metadata names;
pristine ownership uses its existing timestamp name. Heap and TSO readback
inputs are the full existing interpretations at the same actual state, not
replacement memory, arbitrary word facts or fresh cameras.

A pristine timestamp is discarded and cannot be updated into a new pin or
an owned context timestamp share. Therefore this boundary exposes the actual
physical `TsoRead.byteWindow` and `pristineWindow` needed by immutable reads.
The optional context conversion is explicitly restricted to discarded byte
ownership and reuses the existing `TsoContextBytes` discarded-pristine route
at floor zero. It does not require or mint an owned context token.

Every access returns a same-value reassembly wand. No mutable text update
rule is introduced. Readback retains the supplied heap, TSO and text window,
and derives `ReadsBytes` for every agent and view. It is a physical read
consequence, not a successful fetch or page-table translation premise.

## Page boundaries and remaining integration

A virtual window has no hidden alignment or same-page premise. Full-tier
extraction into one physical window requires an explicit `SamePage` bound;
alignment discharges this for two bytes at a two-aligned address and four
bytes at a four-aligned address. A merely two-aligned four-byte instruction
can cross a page boundary. `split_four` preserves both virtual subwindows
without assuming their physical pages are contiguous or equal. Identity-tier
extraction needs no same-page restriction because each byte independently
carries the actual identity pin.

This boundary deliberately stops before whole `InstrBytes`, translation,
fetch execution, or kernel-code ownership allocation. Those later proofs must
supply the real RX claims, exact source-map bytes and pristine resources and
compose the actual translation/read programs. No translation-success oracle,
new camera, Initial allocator or pure-image-to-native-ownership rule is added.

## Validation and remaining integration

The signature checkpoint passed (411 jobs). The completed
`python3 tools/lake.py build Xv6.Kernel.KernelTextDatumLink` passes (687 jobs),
without warnings from the owned prefix. The seven modules are Defs, Spec,
PureProofs, Proofs, WindowProofs, ReadProofs and Link. All approved signatures
remain unchanged. `nativePureSpec`, `nativeSpec` and `nativeWindowSpec` provide
all 36 fields, with concrete existing-registry resource links.

Window normalization obtains the first actual RX claim and uses native mapping
agreement to transport each same-page byte to that PPN. List separation splits
physical/pristine columns and constructs the actual closing wand. Identity
extraction instead uses each byte's identity pin independently. Immutable
readback projects native byte and timestamp authority validity, proves the
latest write is timestamp zero, then applies the existing visible-zero read
law for arbitrary agents and views. Its pure result leaves the original native
heap/TSO resources and byte window available for reassembly.

A fresh complete physical-origin audit checks all 150 declarations, including
private/generated helpers, types, opaque bodies and datatype constructors.
Only propext/Classical.choice/Quot.sound occur, with zero exclusions and no
unsafe/partial or Initial dependency in logical cones. Seven kernel checks
cover both text boundaries, the nonidentity trampoline, a page-crossing
four-byte instruction, exact little-endian halves, noncontiguous physical
page mappings and use of the unconditional native split at page offset4094.

Evidence under `/tmp/xv6-lean-research/`:

- `kernel-text-datum-signatures.log`, `kernel-text-datum-build.log`.
- `KernelTextDatumOwnerAudit.lean`, `kernel-text-datum-owner-audit.log`.
- `KernelTextDatumChecks.lean`, `kernel-text-datum-checks.log`.

Actual translated fetch, source `InstrBytes` constructors and initial code-map
resource allocation remain later integration obligations. No existing frozen
module or umbrella is changed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
