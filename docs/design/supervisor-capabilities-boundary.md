# Native supervisor capability and hart identity boundary

The first resource slice is implemented and frozen as SupervisorBits
Defs/Spec/Proofs/Registry/Link: 578 build jobs and a 234-declaration full
physical-origin audit passed. The remaining integration below is a proposal,
not a completed SIE capability or interrupt-handler theorem. The first
resource contract is the source's bit ownership and live mstatus tie. HartTp ownership and a Bare
function adapter follow as separately reviewed steps. No execution rule
or source capability is replaced by a pure proposition.

The source pin is xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
I read the complete HartTp, SpecMycpu and ProofMycpu files, the relevant
definitions and proofs in IntrDefs, WpNext, CpuOwn, WpSmodeIntr,
RiscvFetchExec, TimerCap, Ktier and WpGpr, and the concrete mycpu call sites
in ProofPushOff and ProofAcquire. Existing Lean capacity, footprint,
context, cycle and function contracts were checked alongside them.

## Exact source structure

| Source | Resource and obligation |
| --- | --- |
| `Xv6Cameras.v:921–924` | One `ghost_varG (mword 1)` camera serves SIE and both SRET mirrors. |
| `RiscvPtsto.v:241–272` | Three canonical **per-era, per-hart names**: SIE, SPP and SPIE. These are already data fields of native `Era.Record`, without allocated ownership. |
| `IntrDefs.v:309–351,385–452` | Live SIE half; kernel-code quarter split into two eighths; handler quarter. SPP/SPIE each have two halves. Allocation and flips retain all pieces. |
| `IntrDefs.v:196–207,595–623,649–678` | `sconf` owns actual privilege, full mstatus, full MIE/delegation and MENVCFG cells, hardware resources, and `minstret_inv`. Its mstatus component is the real cell, SIE half tied to its projection, SPP/SPIE tied halves, and all ten SIE-agnostic status facts. `sconf_at` is an accessor with a restoration wand. |
| `IntrDefs.v:751,932–936,1045–1058` | `intr_off_tok` is an eighth at zero. `intr_count n eb` is an eighth at the saved bit when n=0, otherwise zero. `cpu_hart` also owns actual noff/intena/proc cells, held-lock authority with its depth bound, and hart CSR residue. |
| `IntrDefs.v:2672–2699` | The **current** enabled arm owns an eighth, installed-handler resource, KPT receipt, sepc/scause/stval, traveling SPP/SPIE halves, process claim and `cpu_hart 0 true p ∅`. The disabled arm is exactly an eighth at zero. Stale prose describing an enabled full quarter must not replace this definition. |
| `IntrDefs.v:2762–2770,3224–3229` | `sie_cap` has six conjuncts: tier-indexed free stack, translation slot, arm, own_context, timer capability and tier witness. `sie_cap_gpr` adds active hart, sconf and the TP-pinned GPR file. |
| `IntrDefs.v:2181–2230,2450–2461` | The installed handler is linear stvec ownership plus a SIE quarter and a guarded, hart/context-indexed recursive native WP contract. Its environment and proved environment-move property are retained. It is **not** a freely persistent invariant containing stvec. |
| `HartTp.v:45–137`, `WpGpr.v:98–145` | `tp_pin m` overrides GPR4 with the ambient hart ID. `gpr_file (tp_pin m)` owns actual GPR cells, with x0 represented by the zero-value fact. TP is not a callee-saved software variable or a new ghost camera. |
| `WpNext.v:58–115`, `IntrDefs.v:2940–3005` | A continuation quantifies the destination hart, guarded by `b=false ∨ p=0 → destination=entry`. Off execution collapses this to the entry hart. Generic writes exclude TP; enabled value-sensitive reads need hart-independence. |

The source `sconf_ms_facts` includes MPRV not one, SXL=2, MXR=0, TSR
not one, XS/FS/VS Off, SD=0, a valid nominal MPP encoding and TVM not one.
The proposed translation keeps this complete list; it does not substitute
the smaller fields used by MycpuBare. Source MIE is exactly `MIE_S`,
whereas MycpuBare deliberately accepts a more general delegated mask.
MENVCFG is exactly `0xa000000000000000`: ADUE and STCE are enabled;
PBMTE is zero. Source `hw_config` also includes the actual persistent
hardware cells, static kernel-map claims and generation certificate
(`RiscvFetchExec.v:288–335`). These missing conjuncts cannot be silently
omitted from a definition called full `sconf`.

## First implementation contract: SupervisorBits

Own new `MachCSL/Logic/SupervisorBits{Defs,Spec,Proofs,Link}.lean`, with
an optional separate Registry module and STATUS. Defs/Spec are the first
review checkpoint. The capacity explicitly contains the existing native
register capacity and one `GhostVarG GF (BitVec 1)`; the functor is native
`GhostVarF (BitVec 1)`, not a substitute Boolean assertion or a new
authoritative-map encoding. The coordinator reserved **slot 44** after
`FsCrash.registry` slots 0–43; shared KPT may use 45+ if needed. One bit
slot serves all three names. Registry slot 44 and preservation of all other slots are now proved.
No boot allocation is changed by this resource layer.

Provide raw-name definitions and canonical wrappers through
`era.supervisorInterruptEnable cpu`,
`era.supervisorPreviousPrivilege cpu` and
`era.supervisorPreviousInterruptEnable cpu`. Define `bit`, `sretBits`,
`sretTie`, exact `MsFacts`, and:

```text
msOwn registerName names ms :=
  regPointsto registerName mstatus (own 1) ms ∗
  bit names.sie (1/2) (SIE ms) ∗
  sretTie names ms ∗ pure(MsFacts ms)

armBit names b := bit names.sie (1/8) (if b then 1 else 0)
countBit names n eb := bit names.sie (1/8)
                         (if n = 0 then bit eb else 0)
```

These names deliberately do not claim that `armBit true` is the full
enabled arm. `msOwn` is the exact source `sconf_msown` component, not full
sconf. Planned independently stated Spec laws are native fractional
split/agreement, allocation and full-fraction update; exact
half/eighth/eighth/quarter choreography; traveling SRET agreement/update;
`msOwn ∗ armBit b` entails the live SIE projection equals bit b; and the
source count/arm index consequences. Conserve every allocated fragment.

The useful allocation rule starts with the **already owned actual full
mstatus cell** and `MsFacts ms`, allocates three fresh names, and returns
`msOwn`, two SIE eighths, the handler quarter and both traveling SRET
halves. It does not allocate another register authority or rewrite the
physical register. Names are existential; it cannot mint ownership at
arbitrary preselected `Era.Record` names. Canonical wrappers only use
existing tokens. Installing fresh names into a newly allocated era is a
later boot integration proof and must respect its generation certificate.

The disabled-bit consequence can then be used by native dispatch because
the actual register cell is in `msOwn`. A token with no live-cell tie
cannot imply a machine bit. Ghost flips alone do not execute CSR writes:
actual CSR event WPs must update the physical cell and return the matching
tie before any future on/off execution rule is exported. Retaining the
handler quarter is essential; a raw full ghost update is not evidence
that a handler has been installed.

## HartTp and the first mycpu adapter

The next proposed ownership namespace is `Xv6.Kernel.HartTp`, with
Defs/Spec/Proofs/Link. Reuse Registers and RegisterFootprint, no new
camera. Start with the exact total 32-entry software GPR map and
`pin cpu m`, then define native owned GPR resources using the actual
generated register mapping: x0 contributes only its zero fact and the
31 physical GPR cells use existing register ownership. Keep source full
ownership; separately prove fractional TP access for smaller footprints.
Prove pin-id, non-TP update commutation, `rget_tp`, non-TP read agreement
across harts, and exact lookup/update accessors retaining the remainder.
Do not add TP to the ABI saved set.

At a Bare adapter boundary, split out the actual mstatus and TP cells
once from the common 28-cell footprint and combine them with the bit
tie and pinned GPR fragment. A footprint reconstruction lemma must show
the exact same cells, shares and remaining frame are returned. It is
invalid to pass both an unchanged 28-cell assertion and a full mstatus
cell hidden inside another capability. Other GPR cells come from the
full pinned GPR bundle by a key-disjoint split, with all unused registers
framed. The native MycpuBare theorem then derives SIE=0 by bit agreement
and TP=cpu from real owned values; these are no longer caller pure
hypotheses. Its actual stable-register result restores the same mirrors,
arm and pinned resources at return.

That adapter still has explicit remaining hardware/Bare/physical-stack
prerequisites. It is not named the source `sie_cap_gpr` theorem until
the translation/tier, free-stack, timer, source hardware and remaining
resource bundles are implemented and linked. The initial resource-only
slice has no assumed WP callback. The later function adapter's sole
program continuation is the genuine final returned-cycle WP.

## Missing source integration and ownership coordination

### HartTp Defs/Spec checkpoint

The approved `Xv6/Kernel/HartTpDefs.lean` and `HartTpSpec.lean` spell
out that interface; Pure/Proofs/Link now implement every field. The five
modules are frozen with 349 build jobs and a 155-declaration full audit. `Index = BitVec 5`, `GprFile = Index → BitVec 64`.
`physical` explicitly enumerates x1 through x31 as
`Option {r : Register // RegisterType r = BitVec 64}`; zero is `none`.
There is no register-constructor arithmetic, an unchecked type cast or
out-of-range input. The five-bit domain ensures the final generated-style
arm is exactly x31. `PureSpec` requires proofs that only zero has no
physical cell, nonzero physical keys are injective, the enumeration is
complete/Nodup and there are exactly 31 physical keys. It also requires
equality with the **actual generated** `rX_bits` free tree, not just the
same evaluated result. `readAt` retains its real register-read event.

`file` is a finite separating fold over all 32 indices, full fraction at
each physical cell and the pure zero-value fact at x0. `remainder` is the
same fold with exactly the selected key filtered out. The native Spec
requires a separating equivalence for extracting the selected cell,
replacement/reassembly with the explicit remainder, source lookup/update
restoration wands, the x0 fact, and the corresponding pinned accessors.
`pinnedUpdate` excludes TP; generic unpinned `update` remains available
for legitimate boot/trampoline uses. Replacement of x0 is permitted only
when its supplied pointsto fact proves the replacement value is zero.

`actualTp` couples pinned ownership with the actual register interpretation
to derive physical `registers.x4 = hartWord cpu`. It never infers physical
TP from `pin` alone. `tpAccessor` returns the actual full x4 fragment with
a closer; partial read sharing can then use the existing register camera's
fraction laws. No full physical register file, additional allocation or
new functor slot is introduced. `PureSpec` also preserves the exact
non-TP update and cross-hart read laws. Neither Spec contains a function
WP, an assumed register-read success callback, nor a resource transport
claim between different harts. The complete generated write callback and
the mycpu footprint adapter remain separate execution proof obligations.

The native Spec and PureSpec now have checked proof constructors;
independent implementation review has passed, and the subsequent disabled
Bare function adapter is proved in MycpuOff. Source register-map correspondence is
direct index-by-index; this does not discharge the repository's separate
whole-model Rocq/Lean correspondence obligation.

| Component | Existing native reuse | Remaining proof/resource work |
| --- | --- | --- |
| SIE/SPP/SPIE | Era has the three name families; native GhostVar is available. | Slot 44 membership and the proposed source-exact bit/mstatus layer, then fresh era allocation and real CSR/trap updates. |
| HartTp | Actual register camera, finite fractional accessors and mycpu TP-read plan. | Native pinned full GPR representation, splitting/restoration and boot/trampoline introduction after real TP writes. No ghost allocation is needed. |
| TSO context | `TsoContext.ownContext`, word load/store and exact authored history already implemented. | Context movement across actual scheduler/swtch and environmental transport; no arbitrary re-homing of dirty ownership. |
| Translation/tier | MonoNat slot 3 can express source pending-half at 0, full auth at 1 and persistent receipt 1. Direct native PMP/PTE boundaries exist. | Artifact agent owns shared KPT design, tree/mapping/publication credentials and future accessors. It should also own shared ktier/strans vocabulary to avoid duplicate definitions. Do not replace publication bounds with a global-top receipt. |
| Stack | Native modular physical words and split/join exist. | Exact source `stack_own` at KT0/KT1, mapping/access and arbitrary free-stack recombination. `trap_res false=0`, `trap_res true=90`; no reserve charged to disabled handler code. |
| Timer/retirement | Native arbitrary-counter retirement and all-branch clock rules, with real owned clock cells. | Source timer capability's persistent mcounteren.TM pin and invariant owning arbitrary stimecmp; no deadline assumption. `minstret_inv` is emp in the source; do not resurrect its removed whole-instruction invariant. |
| CPU discipline | LockSet camera slot 26 and canonical held-lock names exist. | Actual context-indexed noff/intena/proc cells, count/held-depth laws, process claims and CSR residue. Their allocation is not implied by the record of names. |
| Enabled handler | Native Iris guarded fixpoints and actual per-event WPs exist. | Exact recursive installed-handler contract, all trap/SRET events, same-context/destination-hart resource return, scheduler no-process nonmigration proof and real handler implementation. No on-arm implementation is part of the first slice. |

`ktier` has the independent order KT0 ≤ KT1 (`Ktier.v:53–76`). It is
not an SIE Boolean. The source translation slot is either pending/Bare
plus owned stvec, or fired/KPT plus TLB residue (`IntrDefs.v:1212–1215`).
The tier witness is needed even in the disabled KT1 arm. Enabled execution
requires the KPT receipt as part of the full arm; source invariant masks
and publication/view credentials remain with the actual accessors.

The mycpu source contract is explicitly disabled and tier-parametric
(`SpecMycpu.v:31–47`). Its mid-function TP read uses `rget_tp`, and each
leaf continuation collapses by `wp_next_off`. Actual callers include
the disabled push_off/pop_off paths (`ProofPushOff.v:333,745,812,1320`)
and acquire after its lock loop (`ProofAcquire.v:512`); they use the
returned pointer for this hart's noff/intena or lock-owner bookkeeping.
A future enabled theorem must return resources at the destination hart,
not frame old hart cells through migration. The context and generation
remain explicit. An off token from an old era or another hart cannot
justify the current physical bit, and disabled interrupts alone do not
prove the scheduler's separate no-current-process migration property.

Validation gates are separate: first prove all resource Spec fields and
audit every physical declaration/type/opaque body/constructor; then
review the footprint adapter before any function claim; finally discharge
the actual handler/scheduler/translation contracts before source-wide
capability or interrupt-enabled claims. No implementation proof is assumed
by this design.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
