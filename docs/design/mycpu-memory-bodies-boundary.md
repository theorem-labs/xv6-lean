# Actual mycpu memory-body boundary

Proposed owner: OpenAI Codex subagent `/root/lean_logic_audit`.
Contract approved and implemented; five modules are frozen after build and audit.
Owned modules:
`Xv6/Kernel/MycpuMemory{Defs,Spec,Plan,Proofs,Link}.lean`, optional local
factor/footprint helper modules if proof size warrants, and STATUS. Existing
Address/BareRead/BareWrite, scalar and return modules remain frozen.

The slice is the four actual compressed memory instructions, including the
actual execute/ExecuteAs selection and their base LOAD/STORE execution bodies:

| Function index | Offset / bytes | Actual body | Address and effect |
| --- | --- | --- | --- |
| 1 | +0x02 / e406 | C_SDSP 1, x1 → STORE 8,x1,x2,8 | SP+8 receives actual RA |
| 2 | +0x04 / e022 | C_SDSP 0, x8 → STORE 0,x8,x2,8 | SP receives actual S0 |
| 10 | +0x18 / 60a2 | C_LDSP 1, x1 → LOAD 8,x2,x1,false,8 | RA receives word at SP+8 |
| 11 | +0x1a / 6402 | C_LDSP 0, x8 → LOAD 0,x2,x8,false,8 | S0 receives word at SP |

These use the already proved MycpuDecode indices and image certificates.
`body i` has exactly the same execute/ExecuteAs definition as the existing
scalar/return bodies; a kernel equality identifies the actual normalized
LOAD/STORE. A successful body returns `Retire_Success ()`. PC selection,
fetch, clock, retirement and SIE/trap handling are later composition layers.

Read sources: pinned xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`,
`ProofMycpu.v:99–136,212–248`; `WpSconfMem.v:3656–3741` gives the precise
C_LDSP/C_SDSP interfaces. Source saved words are arbitrary prior contents;
RA and S0 are not TP, which discharges the source hart-dependent source-value
issue at these concrete registers. Source virtual/tier word and `sie_cap_gpr`
remain stronger than this physical/Bare prerequisite. The later function must
supply those missing regimes and instruction-boundary resources, not rename
these contracts to the source theorem.

Generated paths read in full: `InstsEnd.execute_STORE:16990–16997`,
`execute_LOAD:17449–17458`, `execute_C_SDSP:17657–17660`,
`execute_C_LDSP:17731–17734`; `AddrChecks.ext_data_get_addr:217–220`;
`VmemUtils.get_transformed_data_addr`, `vmem_read`, `vmem_write:429–460`.
The store reads its source GPR before address formation. Address formation
reads actual SP, adds the sign-extended immediate modulo 64 bits and returns
the real Ext_DataAddr_OK wrapper. It then executes the six-read pointer
transform. The memory wrapper runs the existing Bare access. The load's
success tail extends the actual 64-bit result and writes the real target GPR;
no extra read of the old target value exists. Assertions, full-width slices,
extension and every success/error branch must be proved from these programs.

One ten-cell footprint is enough for each body. Its eight configuration keys
are mstatus, current privilege, menvcfg, satp, PMA regions, PMP configuration,
PMP addresses and HTIF base; all have independent DFrac shares. The other two
are SP (fractional) and the selected RA/S0 cell (fractional for store, full for
load). Configuration keys appear once even though address transformation and
Bare access both read several of them. The native proof can split the seven
Bare cells and frame menvcfg/SP/data around that existing memory rule, using
proved `RegisterFootprint.cells_append` algebra, then rebuild all ten cells.
The completed implementation instead widens the concrete memory boundary to
the full ten-cell footprint, folds it directly, and then folds the load's
actual target write through RegisterPlan. This avoids any temporary ownership
split. Pure after_PC/after_nextPC facts document that the target update does
not alter either program counter; no PC read is invented. No 178-cell ownership or new camera is needed.

Configuration for a body states `SupervisorAddress.Config rs Bare`, the
actual corresponding BareRead/BareWrite conditions at its computed modular
address, and matched readable/writable PMA only for the relevant operation.
Thus Supervisor, SXL=2, MPRV=0, MXR=0, PMM disabled, Bare satp, TOR RAM and
HTIF-none are explicit; unrelated hardware fields and platform predicates
remain arbitrary. Eight-byte alignment follows internally from the supplied
context word. No canonical-address bound, global stack no-wrap premise,
fixed reset file, translation or instruction-correctness callback is added.
The source virtual stack regime is not Bare; this restriction must remain
visible in the theorem and status.

Intended pure contracts, expressed schematically with their exact data:

```lean
body_eq (op : Op) : body op = execute (MycpuDecode.normalized (index op))
address_plan ... : RegisterPlan.Returns footprint rs
  (get_transformed_data_addr (.Regidx 2#5) (offset op) (access op) 8)
  (.Ext_DataAddr_OK (.Virtaddr (rs .x2 + offset op))) rs
load_factor ...  -- actual vmem_read plus complete LOAD success/error tail
store_factor ... -- source GPR read, actual vmem_write, all Boolean/error tails
```

These are constructed proofs about the actual residual program, never
premises of the native public rule. Prefix plans must preserve all repeated
reads. Expected store trace: one source read, one SP read, six transform
reads, twenty-one Bare write reads, then one present write event: **29 reads**.
Expected load: one SP read, six transform reads, fifteen Bare read reads,
then one plain read event and one destination write: **22 reads plus one
write**. Compressed ExecuteAs selection contributes pure control only.

Intended native contracts (each quantifies arbitrary actual image/fixed/whole,
generation/era/CPU, context identifier and continuation):

```text
wp_store:
  generationCertificate ∗ cells rs ∗ running ξ ∗
  wordPointsto ξ address (own 1) old ∗ resvFrag rr ∗
  ▷(∀ view, cells rs ∗ running ξ ∗
      wordPointsto ξ address (own 1) (rs source) ∗ resvFrag none ∗ viewLB view
      -∗ WP (continuation (Retire_Success ())))
  ⊢ WP (body store >>= continuation)

wp_load:
  generationCertificate ∗ cells rs ∗ running ξ ∗
  wordPointsto ξ address dq word ∗ resvFrag rr ∗
  ▷(∀ view, cells (write rs destination word) ∗ running ξ ∗
      wordPointsto ξ address dq word ∗ resvFrag rr ∗ viewLB view
      -∗ WP (continuation (Retire_Success ())))
  ⊢ WP (body load >>= continuation)
```

The load includes an explicit reservation frame for composition convenience;
a smaller base rule may omit it and derive the framed version. Fractional
word ownership permits all actual allowed read views through the existing
context proof. Store needs full old word and preserves exact blocked retry
with old reservation/word until success; success clears reservation, authors
the actual log append and preserves the ordinary CPU view. The load preserves
reservation and returns the actual selected-view receipt. Both preserve full
heap metadata/context bookkeeping through the native memory rules. Register
suffix folding must restore the updated ten-cell package after a load without
duplicating read-only cells. No subordinate software/access WP appears as a
public premise; only the genuine final continuation does.

Useful small geometry corollaries identify addresses after the actual scalar
SP push with `StackPhysical.paStk entrySP 1/2`, then save/restore arbitrary
word contents and frame the other slot/remainder through ordinary separation.
They introduce no allocation or source virtual stack claim. A full mycpu
function theorem still needs fetched instruction cycles, retirement resources,
source SIE context and the actual supervisor translation/stack regime.

Validation before freeze: targeted build, full physical-origin/type/opaque-body/
constructor audit of every new declaration, and independent source/native
review. No sorry, custom axiom, native decision tactic or frozen-file change.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
