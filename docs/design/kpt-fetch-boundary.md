# Shared Sv39 instruction fetch from native text resources

This is the implemented native boundary for `Xv6.Kernel.KptFetchHalf` and `KptFetch`.
Source pin: xv6iris arxiv-v1 `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
The approved fifteen contracts are implemented in sixteen modules. The final
Link build passes 1,029 jobs; the full 287-declaration audit has zero exclusions.

## Exact source and generated programs

The source dependency is `InstrBytes.v`53–73, its geometry/window decomposition
and fetch proof281–497, plus `SmodeCorePt.v`974 onward (`s_regime_fetch`),
its translated text/pristine extraction1570 onward, source chunk composition
2359–2448, two-chunk composition near2605, and shared-kernel instance near4700.
These were read alongside the actual generated `Fetch.lean`216–278 and the
existing KptAddress, SupervisorFetchRead and KernelTextDatum interfaces.

| Implemented interface | Exact content |
|---|---|
| `instrBytes` | Source two-alignment; base result owns four discarded RX bytes and a non-RVC low half; RVC owns four bytes with existential high half when four-aligned, two bytes otherwise; errors are False. |
| `KptFetch.factor` | Entire actual generated fetch branch tree with only chunk calls abstracted; PC reads, eager extension checks, all error callbacks, second-half fault address and raw concatenation remain. Its equality to actual fetch is proved. |
| `KptFetchHalf.program/afterTranslation` | Actual fetch_bytes and its exact translation/read continuation, including the generated failed-read address assertion and its original diagnostic string. |
| `KptFetchHalf.PureSpec` | Factor equality, page/alignment geometry, translation success derived from actual returned branch facts plus owned-control Config, and actual register-prefix/one-read factor of mem_read. |
| `KptFetchHalf.Spec.fetch` | Complete native translation and physical instruction read from virtual text ownership. No supplied body WP, successful translation, physical word or per-event read oracle. |
| `KptFetch.PureSpec/ResourceSpec` | Full raw factor, seven-cell uniqueness, next-half alignment, exact word halves; persistent/timeless InstrBytes and actual footprint partition. |
| `KptFetch.Spec.fetch` | Complete generated fetch from the source InstrBytes predicate. The implementation discharges the chunk primitive internally. |

`fetch` chooses a four-byte read at a four-aligned PC because the actual
compiled Ziccif configuration is enabled, even for a compressed result.
At a merely two-aligned PC it reads two bytes; a noncompressed low half
causes a second two-byte chunk at PC+2. Page offset4094 therefore admits two
distinct physical pages. `chunks` contains virtual chunk addresses only and
never assumes their PPNs match or their physical ranges are contiguous.

## Owned registers and source configuration

The final footprint is exactly seven cells: PC, MISA, mstatus,
cur_privilege, pma_regions, htif_tohost_base and menvcfg. Each exposed share is
an arbitrary DFrac. The native KptAddress residue owns SATP, TLB and both PMP
vectors at their existing full shares. Those four are not duplicated in this
footprint. Each chunk returns the residue folded, after its actual TLB refresh,
so the next chunk opens the updated values. The seven auxiliary cells retain
their original values. This footprint was coordinated with the regime-cycle
agent: it can be extracted from that shell without a second mstatus or TLB cell.

Config uses KptAddress's actual Supervisor/SXL2/pmaBoot/HTIF-none values,
plus owned MENVCFG.ADUE=1; the full fetch also requires owned MISA.C=1.
Source SmodeCorePt names full `MISA_C=0x800000000014112D` and
`MENVCFG_S=0xA000000000000000`; this interface uses their relevant getter
conditions and leaves other bits untouched. The existing fixed pmaBoot
specialization is retained, rather than claiming every source PMA layout.
Instruction-fetch effective privilege needs no MPRV-clear assumption.

Text ownership supplies RX mapping, positive canonical VA, physical text/RAM
membership and pristine timestamps. The PPN comes from that actual native
claim. KptAddress supplies the shared path, actual hit/miss selection and
A/D observations. ADUE=1 excludes the disabled error branch from valid outcome
facts; it does not replace the actual read/update program with a success oracle.
The physical instruction read then uses the same-era discarded byte/pristine
window, the residue's actual PMP vectors and the owned PMA/HTIF controls.
The existing plain read request retains its real metadata and leaves the
reservation produced by translation unchanged.

## Guards, receipts and conservation

A `Step` records one chunk's virtual address, independently chosen PPN,
initial hidden residue values, exact tree/path and reference bits, actual
hit/miss/A-D branch, and final instruction-read view. `guard` is a modal
continuation contract with no WP of the translated body. Its branch shape
matches KptAddress: path witnesses first; a miss contributes three walk
guards; the actual A/D branch contributes zero, one or two; then the actual
instruction read contributes exactly one. Unknown observed-word facts stay
inside their A/D guards. Impossible disabled outcomes remain in the raw
factor and are refuted from Config when deriving success.

`guardChunks` composes these guards in execution order. In the two-chunk case,
the second translation has its own residue witnesses and may independently
hit, miss or update. It is not assumed to start from the original TLB.
`traceReservation` applies actual KptAddress reservation updates in order;
plain instruction reads preserve that value. The final resources return all
seven cells, the actual folded residue, the exact final reservation, every
translation/read receipt and the original persistent InstrBytes ownership.
The only WP input is the final continuation at the prescribed result, after
these real event guards and returned resources.

No fresh camera, mapping, physical-memory replacement, initialized ghost world
or Initial constructor is used. Native KPT write-back remains the already
proved shared A/D path; there is no unproved payer callback. Whole source
machine ownership remains inside the existing thread WP invariant.

## Implementation and validation

The half proof derives RX translation success from actual OutcomeFacts and
Config, opens the supplied native text window, invokes KptAddress, performs
the actual pristine memory event, and restores the closed residue. The full
proof constructs finite plans for every accepted source instruction shape.
The plans retain all eager PC/MISA/extension reads. A native induction folds
register prefixes and fully proved half-fetch calls, composing the original
guards, updated reservation and receipts. The source InstrBytes split selects
one or two chunks; it never supplies a successful body WP or fixed physical
word to the public theorem. The compressed two-byte plan uses an internal
zero-extension only as its plan index; exactly two owned bytes enter its read.

One signature error was found before proofs: ordinary `++` syntax allowed Sail
coercions to truncate the proposed halves equality. That failed elaboration was
never verified. With coordinator approval the contract now uses explicit
`BitVec.append`; its 32-bit equality and the physical PPN concatenation are
kernel-proved. The raw generated factor retains the generator's correct `+++`.
A nonzero upper-half fixture checks this boundary.

Files: Half Defs/Spec/PureProofs/ReadProofs/Proofs/Link; full Defs/Spec,
PlanDefs/PureProofs/PlanProofs/GuardProofs/FoldProofs/WindowProofs/Proofs/Link.
All new carrier definitions remain in Defs modules. Public contracts are the
approved Half Pure5+native1 and full Pure5+resource3+native1.

Validation evidence is under `/tmp/xv6-lean-research/`:
`kpt-fetch-build.log`, `KptFetchOwnerAudit.lean`, `kpt-fetch-owner-audit.log`,
`KptFetchChecks.lean`, `kpt-fetch-checks.log`. The audit visits every physical
module declaration including private helpers, all types, opaque bodies and
datatype constructors; only propext/Classical.choice/Quot.sound are allowed.
No unsafe/partial logical dependency or Initial allocator is present. Eleven
kernel checks cover aligned compressed fetch 4, merely-two-aligned fetch 2,
base fetch across 4094, separate nonidentity PPNs, page coverage, nonzero upper
halves, exact result dispatch, raw factor equality and an actual generated
cross-page fetch plan.

Boot allocation of these resources, source boot reachability and the whole
translated function/cycle remain later integration obligations. Config still
uses the existing explicit pmaBoot ambient specialization. Frozen neighboring
files and umbrellas are unchanged.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
