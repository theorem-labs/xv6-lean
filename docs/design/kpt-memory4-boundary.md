# Four-byte native virtual KPT data access

The coordinator approved the six-file, 472-job Defs/Spec checkpoint.
All 21 contracts are now implemented in 19 modules: five each for
SupervisorMemOuter4 and SupervisorWriteEA4, and nine for KptMemory4.
All three native Links compile in the final 1,054-job build. The final
virtual memory rules internally supply every translation, permission,
write-EA and data-event dependency. No existing memory family, generated
model, camera or umbrella was changed.

A strict audit checked all 255 physical declarations, including private
helpers, full types, opaque bodies and datatype constructors. It found
only propext, Classical.choice and Quot.sound, with zero exclusions,
unsafe/partial semantic dependencies or Initial allocator calls.

The source is xv6iris arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The relevant source consumers
are WpSconfMem's width-parametric ordinary load/store rules (2512–2542 and
3196–3244), the four-byte signed load wrappers (2781–2830), and the
push_off noff/intena memory operations in ProofPushOff. These rules retain
the datum's original translation tier and require full ownership for a
store. They are full instruction/source rules; this checkpoint implements
the lower actual virtual-memory dependency, not their GPR/decoder/cycle
or SIE-resource wrapper.

The actual generated definitions were read in Mem.lean460–615 and
VmemUtils.lean236–430, including both error paths, effective privilege,
callback processing, page splitting and the separate write-EA operation.
The implementation reuses the existing KptAddress native translation,
KernelDatumWord4 access/close, SupervisorRead4/Write4 checked-memory plans,
SupervisorDataPma permission plans and context byte read/write WPs.

## Exact public memory boundary

`KptMemory4.addressProgram kind va new` is the actual vmem_read_addr or
vmem_write_addr at width4, ordinary Load.Data/Store.Data, with aq/rl/res
false. `va` remains a 64-bit address; all old/new payloads and the successful
load result are exactly 32 bits. `program` additionally performs the real
transform_effective_address call. Signed or unsigned extension into a GPR
belongs to the later instruction body; neither is substituted here.

The two final native contracts accept the five actual KptAddress auxiliary
cells, its native coherent four-register residue, a running context, the
actual `KernelDatumWord4.word` at the original tier and virtual address,
and a reservation fragment. Their ambient configuration is exactly the
existing KptMemory.Ambient: owned supervisor/SXL, explicit boot-PMA and
HTIF-none, MPRV/MXR zero, PMM disabled and MENVCFG.ADUE one. These are
control facts, not a supplied successful translation or read. The caller
provides no physical word, PPN, map witness, observed PTE, successful WP,
fixed translation outcome or per-step memory callback.

Loads preserve the original arbitrary DFrac. Stores require `.own 1` and
replace precisely those four owned bytes. The five auxiliary cells, folded
actual post-TLB residue, original-tier virtual word, running context and
all original translation receipts return. A load retains the reservation
produced by translation; a store clears the reservation at the actual
ordinary write. One extra later and universally quantified view receipt
account for the data event. KptAddress's dynamic hit/miss and A/D guard
order is retained unchanged, and CompletedFacts occurs inside those guards.

Nine pure contracts expose actual transform and vmem boundaries, derived
successful translation under native word claims, every exception callback
at its original/offset virtual address, and the actual `.Ok false` store
response. Native ownership rules establish the successful branch;
the raw factor does not erase failures. The successful payload is not
assumed in the pure factor or supplied to the public native theorem.

## Four-byte geometry and actual data access

KernelDatumWord4 already proves that four-alignment implies a same-page
four-byte window and preserves alignment and byte offsets after applying
the owned mapping PPN. This includes addresses congruent to4 modulo8 and
the last four bytes of a page; no eight-alignment restriction is introduced.
Its access rule supplies actual native physical context bytes and a
value-polymorphic close continuation. Head-claim facts provide positive
virtual address, physical RAM membership and actual tier/mapping ownership.

The proofs derive physical range from four-alignment plus RAM
membership: the RAM high boundary is divisible by4, so the last byte is
still in RAM. Then the owned boot-PMA table and TOR PMP configuration
justify the actual size4 matching/grants. No caller physical range, PMA
success or translation-success premise is added to KptMemory4.Spec.
Source KernelDatumWord4.Aligned supplies the generated page split `(4,0)`;
the aligned public path performs one translation and one ordinary data
event. Raw residuals keep exception handlers and false responses intact.

## Outer memory bridge

SupervisorMemOuter4 has four pure factor laws and two native rules. The
actual mem_read and mem_write_value width4 each read mstatus and current
privilege and evaluate effectivePrivilege before invoking the checked
supervisor operation. Existing width-independent effective-privilege
plans are reused. Exact factor laws retain callback and metadata behavior
on both response branches; only the actual pure callback is eliminated.
The native rules borrow the two outer cells and four physical-check cells,
return them all, and preserve/replace the actual four-byte context window
with precisely one data-event guard. Physical grant/alignment/range are
internal-layer premises, all derived by the final virtual rule.

SupervisorWriteEA4 retains the original five-cell mstatus/privilege/PMA/
PMP-vector footprint. Its Config names actual supervisor/MPRV, TOR RAM,
size4 matching, writable grant, range and alignment. The pure contracts
are unique footprint, the real pure write_ram_ea announcement at width4,
and a checked finite register plan returning Ok unit. Its native rule
folds that plan and returns all five cells. The EA stage performs the
actual privilege/PMA/PMP reads but no memory event. It is composed before
the separate mem_write_value stage; no write is invented or suppressed.

## Implemented proof and validation sequence

1. Prove the outer factors and native read/write, using the completed
   SupervisorRead4/Write4 kernels and existing effective-privilege plan.
2. Prove the write-EA width4 register plan using generic SupervisorDataPma
   and TOR PMP. Preserve the no-event announcement and all real reads.
3. Prove four-byte geometry and raw vmem boundaries, including update/
   extraction of all32 bits, and reuse width-independent KptAddress
   transform/completion reasoning.
4. Fold the native translation against the original-tier datum access,
   compose the actual data-event plans and close the same virtual word.
   Supply both final address/transformed native rules in an actual Link.
5. Build and strictly audit all new physical declarations, private helpers,
   types, opaque bodies and constructors. Permit only the standard three
   foundational axioms, no unsafe/partial dependencies or Initial
   allocator. Kernel edge checks cover address mod8=4, page-end offsets,
   full32-bit payloads and false/error residuals.

This boundary neither allocates resources nor claims a full push_off,
source capability, decoder/body, interrupt transition or entry/boot
inhabitation. Those consumers may use the completed native rule after its
independent review. Evidence under `/tmp/xv6-lean-research/` is
`kpt-memory4-build.log`, `KptMemory4OwnerAudit.lean`,
`kpt-memory4-owner-audit.log`, `KptMemory4Checks.lean`,
`kpt-memory4-checks.log` and `kpt-memory4-freeze.json`. The 24 kernel
fixtures cover four-versus-eight alignment, page-end and RAM-end bounds,
PPN mapping offsets, all32 payload bits, actual request size/plain flags,
raw false/error returns, no-event EA and reservation behavior. No pure/readback oracle replaces native ownership.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
