# Supervisor translation: next proof boundary

Design proposal, not an implemented interface or a translation theorem. Source
baseline: xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, and the generated
`models/riscv/LeanPaperStock` model. This extends
[the approved mycpu boundary](mycpu-wp-boundary.md).

The recommended next implementation is the **aligned physical-access prefix**:
prove the actual PMA check and non-MMIO classification for an arbitrary source
RAM-granting PMA table, then combine them with the existing supervisor TOR PMP
plan. This serves both instruction fetch and page-table reads. It does not
require a translation-correctness premise, a fixed boot PMA table, or additional
ghost cameras. Bare translation is a separate small register-only follow-up;
the KPT branch needs the tree, mapping, and publication resources described below.

## Source and generated paths checked

| Boundary | Pinned source | Actual generated code |
| --- | --- | --- |
| RAM PMA contract | `RiscvFetchExec.v:88–164`, `RiscvExtras.v:600` | `Pma.lean:349–426`, `Mem.lean:262–402` |
| Physical PTE reads | `SmodePte.v:336–504` | `Vmem.lean:231–239`, `Mem.lean:404–493` |
| Physical supervisor fetch | `SmodeCore.v:257–516`; interleaving rules `SmodeCorePt.v:1321–1530` | `Fetch.lean:216–290`, `Mem.lean:404–493` |
| Bare translation | `SRegime.v:66–180,833–837` | `Vmem.lean:426–447,556ff` |
| Live translation resource | `IntrDefs.v:1212ff,1563ff,1725ff`; `SRegime.v:1337–1390` | `Vmem.lean:556ff` |
| KPT invariant and hart residue | `KptShare.v:55–200`; `PtTree.v:1156ff,1680–1712` | `Vmem.lean:245–424,448–549`; `VmemTlb.lean:280–350` |
| PTE visibility credentials | `CtxValues.v:1–105,375ff`; `KptShare.v:158–195` | `PhysMemInterface.lean:335ff`; actual V1 RAM events |
| Mixed-width fetch ownership | `InstrBytes.v:28–66`; `SmodeCore.v:554–958`; `SmodeCorePt.v:974ff,2359ff` | `Fetch.lean:232ff` |

Some source prose is stale. `SmodeCore.v` explicitly removes the old megapage
machinery near line 534 and uses `KptPt`/`Pt4kWalk`, while prose near line 1228
still describes a fixed index-5 superpage hit. The executable definitions and
current proofs use a three-level 4 KB page-table tree and a direct-mapped
64-entry TLB. Likewise, old comments about `Read_ttw` do not describe emitted
events: `RiscvLang.v:697ff` explicitly records that these fetches and PTE reads
use `Read_plain`.

## First owned implementation proposed

New `MachCSL/Machine/SupervisorPhysical{Defs,Proofs,Plan}.lean` and STATUS only,
after approval. No existing semantics or resource definitions change.

The first theorem should use the already implemented partial
`RegisterPlan.Returns`, with a footprint containing the `pma_regions` cell at
any supplied fraction. A representative signature is:

```lean
-- Proposed interface; exact binder elaboration remains implementation work.
theorem pma_aligned_plan
    (member : (.pma_regions, dq) ∈ footprint)
    (matched : matching_pma_region (rs .pma_regions) (.Physaddr pa) n = some region)
    (supported : SupportedRead access n res)
    (grant : ReadGrant (override_PMA region.attributes .PBMT_PMA) access)
    (aligned : is_aligned_paddr (.Physaddr pa) n = true) :
    RegisterPlan.Returns footprint rs
      (pmaCheck (.Physaddr pa) n access .PBMT_PMA res)
      (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) rs
```

`SupportedRead` is a named, explicit bounded family: fetch widths 2 and 4 with
`res=false`; page-table load width 8 with either reservation flag; ordinary
data load width 8 with `res=false`. `ReadGrant` selects the actual field:
`executable`, `supports_pte_read`, or `readable`. These are projections of the
source RAM contract, not a replacement classifier for other operations.
The source contract also grants writes, all relevant AMOs, PTE writes,
reservability, and misaligned load/store behavior; none is negated or silently
removed from a claimed full-platform contract here.

A companion theorem for actual `check_pma_with_pmp_priority` returns the same
access-info value and uses the same single PMA read: its successful PMA branch
does not call PMP. A second partial plan proves
`within_mmio_readable (.Physaddr pa) n = false` from RAM range and
`rs .htif_tohost_base = none`, retaining its actual HTIF register read. CLINT
and signature checks are pure; the generated eager boolean expression still
evaluates HTIF. First/last-byte RAM bounds must exclude modular wrap, and the
small positive widths remain explicit.

Combining these with the existing TOR entry-0 grant yields the checked-read
register prefix in this exact order:

1. `pma_regions` once; aligned splitting produces one chunk.
2. `pmpcfg_n`, then the `pmpReadAddrReg` reads of `pmpcfg_n` and `pmpaddr_n`.
3. `htif_tohost_base` once.
4. The actual RAM read event, then pure result assembly.

No complete `checked_mem_read` WP is part of the first signature. Its next
composition must expose the real RAM boundary and discharge it using existing
`MemoryReadWP`/`MemoryExclusiveWP` and the correct owned bytes or PTE pin
resources. A separately quantified lower-level read relation is useful as an
intermediate pure plan, but is not a completed memory or translation proof.
The register-only prefix must not assume a returned memory word or an unchanged
TSO state. PTE exclusive reads retain the actual reservation alternatives.

The source PMA predicate quantifies integer widths, including an unrestricted
integer argument in its atomic conjunct; generated Lean APIs use `Nat`.
The bounded theorem avoids claiming an unproved all-integer predicate
equivalence. A later full PMA-contract port must state the source/generated
width-domain correspondence explicitly. For these positive widths, source
`pma_allows_ram` supplies precisely a matching region with the listed grants.

Validation should include ordinary kernel proofs for each supported family,
symbolic unrelated registers and PMA attributes, exact partial footprints, and
full physical-origin/opaque-body axiom auditing. No decoder reflection, giant
full-register snapshots, or new semantic evaluator is needed.

## Bare branch: a separate short follow-up

`bare_inv` owns `satp` with Mode Bare and the PMP configuration, with no TLB
ownership. Its ASID and PPN fields are arbitrary. The proposed register-only
translation lemma should consume actual supervisor privilege, SXL=2,
`satp.Mode=0`, a supported non-shadow-stack access, and the actual
`effectivePrivilege=Supervisor` derivation. For fetch this last derivation is
independent of MPRV; ordinary data accesses use the source MPRV=0 fact.

Actual `translateAddr` first reads `mstatus` and `cur_privilege`, computes
effective privilege, and calls `translationMode`, reading `mstatus` and `satp`
again. Its Bare branch returns the input address with `PBMT_PMA` and unit
translation metadata without a TLB access. This proves that branch only.
The data wrappers' preceding `transform_effective_address` and pointer-masking
reads are a separate prerequisite: source `menvcfg.PMM=0` gives zero masking
length. Bare `translateAddr` alone does not prove those wrappers correct.

KT0 is not a synonym for Bare: identity-mapped kernel text may run under KPT.
KT1 stacks can map to a different physical page. The eventual source theorem
must cover both arms of `strans_inv` and preserve the tier-indexed witness.

## KPT branch: required resources and actual events

`tlb_res_pt root` owns satp (Sv39, ASID zero, PPN=root), the actual TLB vector,
snapshot consistency, PMP configuration, `kpt_inv root`, and publication
credentials. `kpt_body` owns the tree, its canonical agreement, publication
bound, authoritative VPN-to-(PPN,permission) map, and the exact tree spec.
`kmap_at` is a persistent claim for one VPN and its physical PPN/permission.
It is not an all-memory identity assertion. Physical addresses are constructed
from the claimed 44-bit PPN and the 12-bit page offset; `KP_rx`/`KP_rw` controls
which requested accesses that mapping permits.

The source pure geometry and resource layer needs porting before a native
translation theorem:

- Three-level, 9-bit-per-level Sv39 walk geometry, canonical 39-bit addresses,
  PTE validity/non-leaf/leaf permissions, and the returned PPN/page offset.
- All 64 TLB slots, hash collisions, ASID/global matching, fill/update behavior,
  and `tlb_ok_pt` consistency modulo stale A/D bits. No fixed hit index and no
  precondition that all entries already have A/D set.
- `kpt_slot_pin` for eight-byte aligned PTE slots, allowed canonical A/D
  variations, timestamps/publication bound, and `cv_boot_cred`: either the
  current hart has the required view receipt, or boot hart 0 has its own
  publication log-length receipt. Ordinary PTE loads use actual plain TSO
  views and forwarding; a special flat `Read_ttw` rule cannot supply them.
- Native invariant opening/reassembly for the canonical tree/map, and exact
  snapshot custody across exclusive PTE reads and conditional A/D writes.

Existing register, heap/metadata, log, timestamp, view, reservation and native
invariant capacities can be reused. The translation-phase lower bound uses
the existing mono-nat camera with its own explicit source name. The missing
kernel-specific capacities are a ghost map for VPN27 to (PPN44, permission),
the source `kptR` one-shot exclusive-unit/agreement-tree camera, and `kptbR`
one-shot exclusive-unit/agreement-Nat publication bound. The latter is not a
monotone-number authority. Their slots must be explicitly allocated by the
coordinator; this proposal reserves or alters none. Actual TLB ownership uses
the existing dependent register camera, not a second TLB ghost camera.

On a miss, generated `translateAddr` reads satp again through `get_satp`, checks
canonicality, reads mstatus for MXR and SUM, reads the TLB, and performs up to
three ordinary 8-byte PTE reads. On a hit it still checks cached leaf
permissions and may perform an A/D update. `add_to_TLB` reads the vector,
writes it, and reads it again for the generated callback; these are real
subevents. Returned register state may differ in TLB, as the source postcondition
explicitly allows. Translation can also change memory/log/view/reservation;
unchanged register state is not whole-machine preservation.

When `update_PTE_Bits` requests a change, the generated eager Svadu/Svade and
menvcfg.ADUE reads precede an exclusive reread, repeated leaf check, and possible
conditional PTE write. A `.Ok false` conditional write executes
`internal_error "PTE conditional write failed"` in `Vmem.lean:354ff`; it is not
a retry or an ordinary access-fault result. The source snapshot and pin
invariants must exclude that branch in the native proof. The full source
`strans_swp_translate` postcondition returns `resv_any`, so preservation of an
arbitrary incoming reservation must not be added. Source full misa and
`MENVCFG_S=0xA000000000000000` remain useful hardware assumptions; weaker field
projections may be used only where proved sufficient.

## Mixed-width fetch and the concrete mycpu footprint

The actual fetch takes its four-byte aligned path when the PC is 4-aligned
and `currentlyEnabled Ext_Ziccif` returns true, even when the low halfword is
compressed. For this pinned stock model, that extension query is definitionally
`pure true`: `PlatformConfig.lean:2556–2560` delegates to `hartSupports`, whose
`Ext_Ziccif` branch is `true` at line 2156. A full fetch proof must retain and
discharge that query, rather than drop the guard. At a merely 2-aligned PC it reads two bytes; an
uncompressed result then causes a second translation and two-byte read at
PC+2. The second half may cross a page boundary and have a different physical
mapping. There is no generic same-page or physical-contiguity premise to add.
Source `instr_bytes` already accounts for the extra high halfword on a
4-aligned compressed fetch.

The 14 mycpu encodings occupy 32 bytes starting at `0x800018ba`. Its final
compressed JR is at `0x800018d8`, which is 4-aligned, so the pinned Ziccif-enabled aligned fetch path reads through
`0x800018db`. Existing `MycpuDecode` certifies the instruction bytes only,
through `0x800018d9`. A complete concrete fetch certificate therefore needs
two additional following kernel bytes, for a 34-byte union footprint. Both
base instructions are 4-aligned; generic mixed-width fetch still retains the
two-translation alternative for other source call sites. No ELF-symbol parser
theorem follows from these concrete address/image certificates.

After physical and translation layers close, the mycpu proof still owes the
native tier/context access to code and stack, both 8-byte stores and both
8-byte loads without an inserted fence, `tp_pin` CPU identity, real clock and
instruction execution, and the complete disabled-SIE resource reconstruction.
This proposal establishes none of those by a callback or a whole-xv6 claim.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
