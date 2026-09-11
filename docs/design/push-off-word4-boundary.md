# PushOffWord4 normalized instruction boundary

This checkpoint declares actual normalized LOAD/STORE bodies for source
push_off rows 8, 11, 13 and 22. It composes the existing common fifty-cell
supervisor packet with the original virtual four-byte word and the actual
Bare or shared-KPT translation resource. All 23 approved contracts are now implemented in the two native Links;
the full 16-module Link builds in 1,186 jobs and its strict 366-declaration
audit passes with zero exclusions.

The pinned source is `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
Read `CodePushOff.v`, the noff suffix in `ProofPushOff.v:274–410`, the first
noff load at 740–778 and intena store at 852–878. The source normalized
instructions and actual `execute_LOAD`/`execute_STORE` agree:

| Row | Offset | Normalized body | Result |
| --- | --- | --- | --- |
| 8 | 0x14 | LOAD4 signed, a0+120 → a5 | a5 = signExtend64(old32) |
| 11 | 0x1c | identical LOAD4 | same |
| 13 | 0x20 | STORE4, a5 → a0+120 | low32(a5) stored |
| 22 | 0x36 | STORE4, a5 → a0+124 | low32(a5) stored |

One source comment at the second load says zext32; the actual source
constructor, source register update and generated `extend_value false`
use sign extension. The checkpoint preserves that executable behavior.
All addresses use ordinary modular 64-bit addition; no special CPU-address
value, nonnegative noff, noff bound, or intena Boolean is assumed here.
Source function proofs must establish those higher-level invariants.

## Public body contract

`PushOffWord4.Spec.body` handles all four operations and both actual
`MycpuRegimeShell.Regime` constructors. Inputs are the generation receipt,
common packet, running context, `KernelDatumWord4.word` at its original tier,
reservation fragment, arbitrary frame, and genuinely guarded continuation.
Load permits arbitrary DFrac; store requires the full share. The Bare route
uses the existing `Admits` compatibility (identity-tier only); the KPT route
retains either original tier. No tier is upgraded or silently replaced.

The packet supplies the real operands a0/a5, all five ambient controls,
source mstatus facts and interrupt-bit resources. Seven cells are borrowed
for a KPT body, with forty-three remaining cells framed. The four-register
KPT residue remains separate and is returned with its actual updated TLB.
Bare instead opens its supplied existential SATP and two PMP cells, patches
only those three projections, and borrows ten of the resulting fifty-three
cells. Its remaining forty-three cells and every source bit/x0 fact are
retained. A pure patch/configuration bridge uses these actual existential
values rather than the unowned SATP/PMP projections of the control file.

`afterMap` changes only a5 on loads; its new value is signExtend64(old32).
Stores preserve the whole GPR map. Both preserve a0, SP, all effective
addresses, and the complete control file. The same original-tier word is
returned, with low32(a5) after stores. The arbitrary frame can contain the
other noff/intena field, stack words, source timer or additional receipts.

KPT outcomes preserve the full existing hit/miss and A/D guard nesting,
branch-local CompletedFacts, evolved reservation and all translation
receipts, followed by exactly one data-event guard and view receipt. Bare
has exactly one data-event guard and view receipt, preserves the input
reservation on a load and clears it on a store. Outcome is indexed by
regime so a Bare branch cannot invent a KPT translation receipt.

The pure factor exposes actual register read order (store reads a5 before
a0), base-address/extension hooks and the actual transformed four-byte
virtual-memory program. Raw memory/translation errors remain in that
program. The LOAD error returns its actual error result; STORE success
ignores either Boolean as the generated instruction does. Native ownership
will prove the real permitted response, rather than assuming it. Compressed
expansion is separately stated using the existing decoded table; the public
body itself starts at the normalized instruction and excludes fetch,
decode, PC advance, postlude clocks, and cycle restart.

## Necessary Bare prerequisite

Existing `SupervisorBareRead`/`SupervisorBareWrite` are fixed to eight bytes.
The missing layer is the four-byte Bare virtual-memory factor and native
composition, not a new memory model. `PushOffWord4Bare{Defs,Spec}` declares
that bounded prerequisite using an eight-control-cell footprint:
mstatus, privilege, MENVCFG, SATP, PMA, both PMP cells and HTIF.

Its pure contracts connect the actual transform and vmem functions to
one size-four read/write event using existing generic Bare translation,
`SupervisorMemOuter4`, `SupervisorWriteEA4`, and physical
`SupervisorRead4`/`SupervisorWrite4`. All metadata/tag/error/false response
behavior is inherited by the exact OneRead/OneWrite judgments. No new
oracle, event or camera is introduced. The actual EA stage remains the
existing no-memory-event computation.

This internal native prerequisite takes a physical context byte window and
explicit alignment/RAM geometry. **The public body caller does not supply
these.** Its `identityWord` resource accessor derives them from the actual
identity-tier virtual word, its mapping claims and physical bytes, retaining
a value-polymorphic closing wand for stores. Four-alignment and the RAM
interval geometry supply the last-byte bound; no eight-alignment premise
or current physical-value equality is added. Explicit hardware Config uses
same-hart pmaBoot, disabled HTIF and PMM, Supervisor mode, and actual
supplied Bare/TOR cells. Only the KPT configuration requires ADUE=1.

## Approved checkpoint and completed implementation

The original approved declaration checkpoint comprised four files:
`PushOffWord4BareDefs`, `PushOffWord4BareSpec`, `PushOffWord4Defs`,
`PushOffWord4Spec`. They retain all 23 approved contracts: four Bare pure and one Bare
native, fourteen body pure, three resource equivalences/accessors and one
regime-dispatch body WP. All subsequent proof modules remain within the
PushOffWord4 prefix.

Implementation closes the size-four Bare factor/native event bridge,
actual normalized operand/tail plans and packet partitions, and dispatches
to KptMemory4 or the Bare prerequisite internally. Eighteen kernel fixtures
include actual generated-body load execution and actual store-prefix
requests, exact source indices, sign-bit/truncation examples, offset 124
four-but-not-eight alignment, both instruction Boolean tails and errors.
The strict physical/private/type/opaque/constructor audit covers all 366
declarations, uses only the standard three axioms, and has zero exclusions.
Detailed build, fixture and freeze evidence is recorded in STATUS. No existing frozen module or umbrella is owned or modified.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
