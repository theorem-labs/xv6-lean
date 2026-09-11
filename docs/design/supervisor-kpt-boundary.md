# Supervisor KPT/Sv39 implementation boundary

This is a source-validated proposal, not an implemented translation theorem.
The `TsoPinnedRead` resource slice is implemented and frozen (five modules,
501 build jobs, 55 audited declarations), as is the `TsoPinnedStore` companion
(five modules, 503 jobs, 43 audited declarations). Their exact scopes are in
`MachCSL/Logic/TsoPinnedReadSTATUS.md` and `TsoPinnedStoreSTATUS.md`. Canonical
PTE and translation stages below remain separate work; the ownership gates
do not establish an event WP on their own.
The next reusable boundary is the **context-free pinned page-table ledger**:
read a slot at every permitted TSO view, and preserve its byte families through
an actual A/D write-back. Ordinary context-word ownership uses `payNone` and
cannot supply this boundary. The existing Bare memory bodies remain useful
instruction-wrapper prerequisites; disabling SIE does not make SATP Bare.

Sources are `.upstream/xv6iris/iris/` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. Generated references are under
`models/riscv/LeanPaperStock/`, from the pinned Sail source
`23dcf8fd923eb8a1958795393d2975632aa940b2` and the repository's reviewed adapter.
This proposal follows the cited complete definitions and relevant proofs,
including the complete generated page-walk/translation and A/D-update bodies.
It does not assert whole-model Rocq/Lean correspondence.

## Source contract that must survive

`ProofMycpu.v:99–136,212–248` uses the tier-polymorphic stack load/store rules
in `WpSconfMem.v:3656–3741`. The source virtual byte assertion
(`TsoCtx.v:616–650`; `RiscvPtsto.v:1188–1255`) includes a persistent
`kmap_at (svpn va) ppn KP_rw` claim, positive virtual-address bound
`va.toNat < 2^38`, physical RAM at `pa_of ppn va`, the translation-tier pin,
and the context-indexed physical byte/timestamp resource at that physical
address. Code uses the corresponding execute permission class.

`KT0` pins the translation to identity; `KT1` permits the claimed nonidentity
mapping and requires the KPT regime witness (`Ktier.v:1–120`). These are not
the `PtTree` slot-ownership alternatives `KTier B` versus `UTier ξ`.
In particular, a nonidentity kernel stack cannot be served by a Bare theorem.
The eventual virtual word and stack algebra must retain all of these claims
while exposing the existing physical context-word resource at the translated
address. No global stack no-wrap condition is needed.

The disabled-SIE capability still contains `strans_inv`
(`IntrDefs.v:1200–1233`): either the actual Bare pending resources, or the
installed KPT residue. The latter is `KptShare.tlb_res_pt` at lines 179–192:

- Full SATP ownership with Sv39, ASID zero, and its actual root PPN.
- Full ownership of the actual 64-entry TLB and a persistent canonical-tree
  coherence snapshot. The TLB need not be empty and its A/D bits may be stale.
- The existing source-compatible two-cell PMP grant, `kpt_inv root`, and
  publication credentials.

The shared invariant (`KptShare.v:86–98`) is exactly an existential tree,
mapping, and bound: full `kptree_own B 2 t`, canonical-tree agreement,
`kpt_bound B`, mapping authority, and `kpt_tree_spec_gen root M t`.
There is no current context or hart in its body. `KptGhost.v` uses a one-shot
exclusive token becoming agreement on `ptree_canon t`; it does not use an
A/D-monotone authority. Its separate bound agreement also carries a log-length
receipt. The old prose at the start of `KptShare.v` predates this definition;
the current definitions and proof bodies determine the port.

## First native resource contract

Reuse `Tso.physLedgerPin` and `Tso.pinMapOwn` unchanged. They already name the
actual heap byte slot 0 and timestamp slot 1, with payload
`payPin allowed bound`; `Heap.interp` supplies the full existing metadata
component. Reuse `TsoStore.Capacity`, `Names`, `Transition`, finite maps,
`windowMap`, and window injection proofs. No new camera or name is required
for this first boundary.

The proposed new `TsoPinnedRead{Defs,Spec,Proofs,Link}.lean` and optional
`TsoPinnedReadPure.lean` expose these concrete predicates and laws:

```text
ownAnchor names h a p :=
  ∃ i msg byte, ⌜p = i+1 ∧ msgByte msg a = some byte ∧ msg.author = h⌝
    ∗ History.logElem names.logEntries i msg

bootCredential names cpu B :=
  Views.viewLB names.views names.logLength cpu B
  ∨ (⌜cpu = 0⌝ ∗ Views.llb names.logLength B)

slotBytes names a dq bytes B sets :=
  [∗ j ∈ range bytes.length] ∃ floor time,
    ⌜floor ≤ B⌝ ∗ physLedgerPin names (addressAdd a j) dq bytes[j]
      time floor (sets j)
    ∗ (⌜floor = 0⌝ ∨ ownAnchor names 0 (addressAdd a j) floor
       ∨ Views.viewLB names.views names.logLength 0 floor)
```

Here `bytes[j]` is accessed with the range proof; no default byte is part of
the contract. Native definitions will use the existing exact capacity/name
arguments, and will provide the eight-byte `nthByte word` specialization.
The pure anchor fact is taken from actual history authority and `LogRep`, not
from an assumption that the reader's current view is high enough.

The intended checked entailments are:

```text
pin_valid:
  tsoInterpAt image g -∗ physLedgerPin a dq byte t floor S -∗
    ⌜PinOK image g.log a floor S⌝

author_read (floor ≤ p):
  tsoInterpAt image g -∗ physLedgerPin a dq byte t floor S -∗
  ownAnchor h a p -∗
    ⌜∀ view, ∃ b, read image g.log h view a = some b ∧ b ∈ S⌝

slot_read:
  tsoInterpAt image g -∗ bootCredential cpu B -∗ slotBytes a dq bytes B sets -∗
    ⌜∀ view ≥ g.views cpu, ∀ j < bytes.length,
       ∃ b, read image g.log cpu view (addressAdd a j) = some b ∧ b ∈ sets j⌝
```

Preserving/frameable forms return the input linear resources with the pure
fact. `author_read` ports the actual settle/maximal-visible-message argument
of `TsoMemPa.pin_ok_author` at lines 2343–2370, then
`CtxValues.cv_own_read` at 323–348. `slot_read` ports all three slot-anchor
arms and both credential arms in `CtxValues.cv_slot_read_ok:426–486`.
Requiring every hart's view to exceed the publication bound would discard
the source boot-hart forwarding case and is not an acceptable substitute.

The next separately frozen companion is
`TsoPinnedStore{Defs,Spec,Proofs,Link}.lean`, with optional pure helper module.
Its map theorem is the exact registered-pin form of
`TsoCtx.ledger_store_pin_ok:3596–3620`:

```text
SameDomain old new →
(∀ a v, new[a] = some v → v ∈ sets a) →
TsoStore.Transition before after new author →
heapAt before.memory -∗ tsoInterpAt image before -∗
pinMapOwn old (own 1) floors sets ==∗
  heapAt after.memory ∗ tsoInterpAt image after ∗
  History.logElem before.log.length (decode new, author) ∗
  [∗ a ↦ byte ∈ new]
    physLedgerPin a (own 1) byte (before.log.length+1) (floors a) (sets a)
```

The update retains each old floor and allowed set, advances the physical
byte and timestamp together, retains all off-address timestamp payloads,
and preserves full heap metadata. The actual memory is the decoded overlay;
the log appends one message authored by the specified agent. Source view
monotonicity and post-log bounds are retained, so the same theorem can serve
ordinary unchanged-view writes and exclusive view-advancing writes. Its
window adapter uses the source `n ≤ 2^64` injection bound and per-offset
floors, not a fresh stack restriction (`TsoCtx.v:4190–4274`).
This theorem is a resource update for explicit state equations; the later
event rule must derive those equations from each actual successor.

## Canonical PTE and actual event boundary

The first pure PTE companion, proposed as
`Machine/PteCanonical{Defs,Proofs}.lean`, should transcribe
`PtTree.v:944–980,1070–1090,1130–1190` exactly:

- `pteCanon` clears A and D; `pteSetAD` changes only those bits.
- For nonleaf PTEs every byte set is a singleton. For a leaf, only byte zero
  admits the four A/D variants; all upper bytes are singletons.
- Membership of all eight assembled bytes gives exact equality for an
  interior PTE, and canonical equality for a leaf. Arbitrary mixtures of
  permitted byte observations remain in the leaf's canonical class.
- Actual `update_PTE_Bits` preserves that canonical class and its allowed
  byte sets for the supported access classes. Prove the generated expression,
  not only a separate mathematical setter.

`kpt_slot_pin` then combines the existing aligned eight-byte physical window
with the exact per-byte anchors above. Full tree ownership and publication
allocation are later separate modules. `Era.Record` already contains the
three runtime names `kernelMap`, `kernelPageTable`, and
`kernelPageTableBound`; this does not mean their resources are allocated.
Their required cameras are a finite mapping ghost map and two one-shot
agreement cameras over the exact tree and Nat. No slot is assigned here:
the current `FsBlockGhost` registry already occupies slots 0–41 (42 onward
is free), and any extension
must be coordinated and preserve every existing capacity.

The next event WPs will consume these resources inside `kptN`, construct the
actual native `MemoryReadWP`/`MemoryExclusiveWP`/`MemoryWriteWP` accessors,
and close the invariant at each real event. There is no invariant left open
across the exclusive read and conditional write. A supplied software WP,
page-table success callback, whole-step correctness fact, or reservation
preservation oracle is not part of the public contract.

For an ordinary PTE read the conclusion is the appropriate exact/canonical
predicate of the returned 64-bit word at every permitted view; it need not
equal the current physical leaf word. The exclusive read returns the actual
current word and snapshot reservation. The subsequent conditional write
uses that held snapshot and full slot ownership to establish the real
write result and reclose the pinned slot at the new timestamp. Existing
`SupervisorRead`/`SupervisorWrite` pure prefix machinery is reusable; their
payNone context-word native rules are not the pinned-slot rule.

## Generated trace and failure obligations

`Vmem.lean:221–249` defines the three PTE builtins. Ordinary `read_pte` is
`Load PageTableEntry`, eight bytes, all three flags false. It produces the
actual V1 plain read; it must not be replaced by a flat-memory table-walk
read. Exclusive reread sets the reservation flag; conditional write is
`Store PageTableEntry` with its reservation flag set. The existing physical
read configuration gives five register reads (PMA, two PMP configuration
reads, PMP address, HTIF) before the memory event. The new exclusive/write
prefix certificates must retain their actual PMA classification and prove
the corresponding event path, rather than inherit an unchecked count.

`Vmem.lean:325–375` has these actual update branches:

| Actual condition | Required effect and residual |
|---|---|
| Initial A/D update unnecessary | No reread or write. |
| Update needed, ADUE disabled | `PTW_PTE_Needs_Update`; no fabricated success. |
| ADUE enabled | Read MENVCFG, perform an exclusive PTE reread, and recheck that returned leaf. |
| Reread already has required A/D bits | Return that reread word without a write; the reservation may remain present. |
| Reread still needs an update | Perform the actual eight-byte conditional write with the recomputed PTE. |
| Conditional write returns true | Return the updated word. |
| Conditional write returns false | Actual `internal_error` at `sys/vmem.sail:226`; this is not a retry loop. |
| Memory error or invalid reread | Preserve the `PTW_No_Access`/leaf-check error conversion. |

The source supervisor configuration has MENVCFG
`0xA000000000000000`: ADUE=1, STCE=1, PBMTE=0. It does not set A/D bits in
every PTE. The native theorem must prove that the actual configured RAM
events cannot return the false/error branches under its owned resources;
the pure factorization must retain those branches. Actual blocked exclusive
reads clear the local reservation, blocked writes preserve it, and successful
writes clear it. Blocking remains a real successor; it is not erased by a
successful finite trace.

`pt_walk` (`Vmem.lean:379–425`) reads the three Sv39 levels for the source
4 KiB tree. It does not itself perform A/D write-back. `translate_TLB_miss`
does so after the walk. A miss therefore has three ordinary PTE memory reads,
plus zero or one exclusive reread and zero or one conditional write. A
coherent hit has zero ordinary walk reads but can still take the reread and
write-back path. Hits, empty misses, and foreign-tag misses all need proofs.

The generated TLB effects must remain explicit (`VmemTlb.lean:259–360`):
lookup reads TLB once; miss installation reads TLB, writes TLB, then reads
TLB again for the pure callback. A changed hit reads then writes TLB; an
unchanged hit leaves it alone. Only TLB may change in the translation
register footprint. Other physical register ownership is framed, using
arbitrary permitted fractions and full TLB ownership.

The generated validation code also contains real eager register effects in
Boolean expressions. `pte_is_invalid` reads MENVCFG twice and MISA three
times through the Svpbmt/Svnapot/Svrsw probes
(`VmemPte.lean:263–280`, `PlatformConfig.lean:2580–2586,2637–2639`). A valid
level-zero `check_leaf_pte` adds its Svnapot MISA read and PBMTE MENVCFG read
around that invalidity check. These cannot be dropped because the pure
source PTE validity facts already decide the result. Aggregate full-walk
register counts will be certified by the actual plan decomposition; this
proposal does not present an unproved whole-function trace certificate.

## Eventual public translation theorem and completion test

After the pinned gates and exact canonical tree layer, the intended native
`translateAddr va access` rule takes one finite fractional register footprint
covering status, privilege, MENVCFG, MISA, SATP, PMA, PMP configuration/address,
and HTIF, plus full TLB, the real generation certificate/reservation fragment,
`kpt_inv root`, coherent TLB snapshot, publication credentials, and the
permission-class mapping claim. It returns the actual translated
`pa_of ppn va`, `PBMT_PMA`, unchanged non-TLB registers, a coherently updated
TLB, and the actual residual reservation (existential where A/D branches
vary). The actual status/SXL/MPRV/SATP/extension facts are explicit source
configuration facts, not a reset register file. MXR/SUM and all four A/D
variants must be covered by the claim-specific permission proof.

The canonical positive VA bound comes from the source virtual claim; the
tree supplies RAM, alignment, and PMP coverage for each PTE slot. The native
proof opens and restores the invariant at each memory event, consumes no
caller-provided translation success premise, and handles every TLB branch.
Only after this rule and virtual context-word/stack bridges are checked may
the current Bare `mycpu` memory bodies be generalized to the source KPT
regime. Fetch must use the same installed-table interface at execute
permission. The remaining SIE/shelter/cycle/function assembly stays explicit.

Proposed implementation order is: freeze/audit `TsoPinnedRead`; freeze/audit
the pinned store and pure PTE byte-family algebra; then request the concrete
KPT tree/camera and native PTE-event contracts before broad translation code.
Each checkpoint needs source correspondence, all-definition/type/opaque-body/
constructor cone auditing, and ordinary kernel proofs. No current closed
JAL or spinlock theorem is being promoted to an xv6 `mycpu` theorem here.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
