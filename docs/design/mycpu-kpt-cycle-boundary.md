# Actual indexed shared-Sv39 mycpu cycle

This is the implemented native indexed cycle for
`Xv6.Kernel.MycpuKptCycle`. All thirteen pure and two native contracts are
proved in eight modules. The final Link build passes 1,112 jobs; the full
131-declaration audit has zero exclusions.

Source pin: xv6iris arxiv-v1 `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
Read the complete existing MycpuActive definitions/plans, MycpuRegimeShell
contracts and native proofs, the fourteen CodeMycpu/ProofMycpu instruction
steps, source SmodeCore.v145–260 and the actual generated Step.lean
run_hart_active/try_step bodies. The concrete transition boundary is
MachCSL.Machine.Node.cycle and its actual pure-to-cycle restart rule.
The shared body owner independently implemented and audited MycpuKptBody;
this cycle uses its exact route-indexed outcomes and fixed stack anchor.

## Source packet and hardware

The only packet is the existing fifty-cell MycpuRegimeShell resource:
source control/retirement/clock cells, all 31 actual pinned GPR cells,
msOwn/off/bit resources and the software x0 fact. SATP, TLB and both PMP
vectors remain exclusively inside the separately folded KptResidue.
The code bundle is the existing fourteen virtual RX/pristine windows whose
union is the actual 34-byte ELF-backed fetch footprint. Stack ownership is
the body's fixed virtual pair at entrySP−8 and entrySP−16; it is not
reindexed by an intermediate scalar SP change.

`Config control` specifies actual owned source register values: Supervisor,
HART_ACTIVE, ELP zero, MISA 0x800000000014112d, MENVCFG
0xa000000000000000, mie & ~mideleg = 0, pmaBoot and HTIF-none.
The PC is independently tied to the chosen instruction index. SIE=0 and
MsFacts, including SXL, come from native packet ownership, not a supplied
interrupt or translation success oracle. The memory-only `StackReady`
premise is precisely the body's source SP/save-area relationship. The
fourteen-step function's phase invariant must establish it later.

## Pure and register boundary

The factor law retains the actual dispatch pending-interrupt branch and the
full actual fetch/landing/decoder tree. New plans operate directly on the
fifty owned cells. In particular the old Bare MycpuActive footprint cannot
be widened wholesale: it includes translation registers now owned inside
the residue. The new native decoder justifies every actual CSR read by
its owned literal Config, then transports the existing kernel-checked decoder
certificate to a RegisterPlan. The pure snapshot certificate alone is not
used as a native decoder or successful-body assumption.

The pure contracts comprise: actual active factorization; actual decoder
read plan; actual no-interrupt plan under SIE=0; decode/landing/setNextPC
prefix; actual execute/ExecuteAs tail; prepared-entry compatibility;
source fetch/body configuration; configuration through setup, body and
arbitrary accepted clock successors; exact body nextPC and completed PC.
Return clears the low target bit through the existing actual retPC rule;
other instructions advance by their actual decoded width.

## Native active and cycle rules

`Spec.active` executes actual run_hart_active 0, internally applying the
indexed fetch rule, the owned register decoder/landing/setNextPC plans and
the complete indexed body rule. Its continuation sees the actual successful
Step_Execute with exact instbits. Inputs include neither a fetch/body WP nor
a translation, decode or execution success certificate.

`Spec.cycle` additionally executes setup, the successful retirement suffix,
the optional real clock path for arbitrary input tick, and the genuine
restart. Its only final WP premise is the next actual cycle under the
restart guard. The returned `Completed` relation allows every actual clock
successor; no fixed counter/time/mip result or fixed Bare guard count is
substituted.

Both rules retain the existing fetch guardChunks and their path witnesses,
all hit/miss/A-D alternatives and exact facts beneath those guards. The
body guards add nothing for a register instruction. For a memory body they
retain the actual translation guards, observed CompletedFacts and data-read
or data-write event guard. No shared observed word is moved outside its
actual branch. All returned translation/view receipts remain available.

Reservation threading is fetch traceReservation, then the route-specific
body reservation update, then actual restart to none. The active boundary
returns the exact first two stages. The cycle boundary returns none together
with the full packet, coherent updated residue, original code, running
context, updated fixed stack pair, all receipts and arbitrary caller frame.
No resource is allocated and no initial-world constructor is used.

## Implementation, validation and limits

`PlanProofs` constructs direct fifty-cell register plans. Its structural
snapshot-to-plan induction rejects missing register values, writes and memory
events; every actually used snapshot register belongs to the owned packet.
The actual active factor, landing checks, C-extension checks, PC read and
nextPC write preserve source event order. `PureProofs` supplies every approved
pure field, including exact return/advance and arbitrary clock-successor
configuration preservation.

`Resources` proves modal guard transport, the exact native body finish shape
and full packet decomposition/reassembly around a checked finite register
prefix. The unchanged bit/x0 and translation resources are framed throughout.
`ActiveProofs` discharges dispatch using native off ownership, invokes the
actual indexed fetch internally, executes native decode/landing/setNextPC and
then the actual indexed body. `Proofs` composes actual shell setup, active,
retirement/clocks and genuine restart. `Link` supplies the actual body Spec;
its exported nativeSpec has no component WP or Spec parameter. KptFetch and
RegimeShell are likewise concretely supplied inside the proof implementation.

Eight files: MycpuKptCycle{Defs,Spec,PlanProofs,PureProofs,Resources,
ActiveProofs,Proofs,Link}.lean. Build: 1,112 jobs without warnings.
Fresh audit: all 131 physical-origin declarations, private/generated included,
with complete type/opaque-body/constructor dependency traversal; standard
three axioms only, zero exclusions, no unsafe/partial or Initial dependency.
Six kernel checks cover all thirteen forward instruction boundaries, an odd
RA return, share-independent keys, exclusion of translation-owned cells,
the deliberately permissive clock preservation relation, and the fully
linked native Spec without a component interface premise.

This is one indexed actual cycle, not yet the complete fourteen-cycle mycpu
function. Function phase/stack restoration, final arithmetic result, source
boot reachability and native entry-resource allocation remain separate
obligations. The body agent owns the independent fixed-anchor body family;
no frozen neighboring family or umbrella was changed.

Evidence under `/tmp/xv6-lean-research/`: MycpuKptCycleOwnerAudit.lean,
MycpuKptCycleChecks.lean and mycpu-kpt-cycle-{build,owner-audit,checks}.log.
The initial approved signature build remains in
mycpu-kpt-cycle-signatures.log (585 jobs). STATUS records the frozen handoff.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
