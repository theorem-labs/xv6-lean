# Single-tree TLB provenance and exact register operations

The owned prefix is `Xv6/Kernel/TlbCoherence{Defs,Spec,...}.lean`, with a
separate PlanSpec and narrow WordProofs/Proofs/PlanProofs modules. All six
modules compile (449 jobs); Link constructs all twenty pure laws in
nativeSpec and all four actual plans in nativePlanSpec. No existing
frozen file is changed.

I read the complete relevant source coherence sections PtTree.v:1680–2111
and the entry/tag/hit/blocked-query closure at 2174–2541, CommonWalk.v:
795–806, KptShare.v:153–220, all generated VmemTlb.lean and the generated
translate_TLB_hit/miss control in Vmem.lean. Source pin:
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476; generated model pin:
23dcf8fd923eb8a1958795393d2975632aa940b2. These are source correspondences,
not a formal Lean/Rocq model equivalence.

The exact source single-tree relation is retained:

```
CacheOf asid tree query ent :=
  ∃ origin p2 p1 p0 a d,
    Maps tree origin p2 p1 p0 ∧ hash origin = hash query ∧
    ent = entry asid origin p2 p1 (setAD p0 a d)

Coherent asid tree tlb :=
  ∀ query ent, tlb[hash query]? = some (some ent) →
    CacheOf asid tree query ent
```

The actual vector has all 64 optional entries. The hash is the generated
low-six-bit function; no injectivity or occupancy restriction is assumed.
`index_surjective` and `all_slots` explicitly connect this source-shaped
quantification to every physical index. Foreign VPN tags and collisions
remain permitted. Source coherence does fix stored entries to its ASID;
it does not allow arbitrary foreign-ASID entries under that same relation.
The generic lookup plan nevertheless covers every arbitrary vector entry,
and tag laws quantify the requested ASID separately, including the actual
global-entry exception.

`entry` reuses the frozen Sv39Tlb.entry at level zero. It stores the
sign-extended 45-bit origin VPN, zero level mask, the source ASID, cached
64-bit PTE, its exact 44-bit PPN, the installing walk's leaf-slot address
`Physaddr (PtTree.addr0 p1 origin)`, and the complete accumulated global
bit from raw p2, raw p1 and the cached leaf. No G/RSW restriction is added.
A subsequent root or SATP value cannot replace that origin address.

`Variant current cached` means exactly two arbitrary replacement A/D bits.
It is equivalent to word canonical equality, not equality with current
physical memory and not a monotone A/D ordering. Both cached clear and
cached set bits are permitted. Validity of a cached leaf, leafness, NAPOT
absence and PBMT zero are derived from Maps and leaf-specific A/D
stability. They are explicit conclusions of cache_properties, not extra
coherence assumptions. Canonicalization of invalid pointer words is never
used to assert validity.

The pure Spec has twenty contracts covering:

- Every hash slot, empty vectors and the precise A/D variant relation.
- Actual match_TLB_Entry: tag equality plus matching ASID or accumulated G.
  Cache provenance can be specialized to the queried VPN only after this
  real tag test. Matching foreign requests does not change stored ASID.
- Canonical tree transport per entry and for the whole vector, enabling
  coherence relative to a persistent shared-tree snapshot.
- Walk fill with any A/D variant, including the current leaf; A/D-only
  tree updates preserving all resident entries; exact cached-entry refresh.
- General lookup result provenance and blocked-VPN misses, including a
  foreign resident entry at the same hash.
- Actual tlb_get_pte, tlb_get_level and tlb_get_ppn projections. PBMT is a
  genuine Sail program and therefore belongs to PlanSpec.

The source set-leaf lemmas list four updated-leaf classification premises.
The new contracts derive those from Maps and A/D stability instead of
requiring redundant caller premises. This does not extend stability to
nonleaves. The proof still uses exact setLeaf path behavior and preserves
other VPNs without a hash or physical-page injectivity assumption.

`filled` reuses the actual Sv39Tlb.filled vector update. `refreshed` is the
actual `vectorUpdate old idx (some (tlb_set_pte ent word))`. The refresh
coherence law requires the selected actual resident entry and an A/D
variant of its cached word. `set_pte_entry` proves that updating only
pte agrees with rebuilding the source walk entry, because A/D changes
preserve PPN/global/tag/origin fields. No refresh rewrites unrelated fields
or inserts a new origin address.

PlanSpec has four concrete RegisterPlan.Returns contracts:

1. lookup_TLB performs its one real TLB read and returns the exact pure
   lookupValue branch (empty, foreign-tag rejection or matching hit).
2. add_to_TLB performs the actual read, level-zero write and final callback
   read; use the frozen Sv39Tlb.fill_plan and retain the universal callback
   read rather than replacing the command with a direct vector update.
3. write_TLB with tlb_set_pte performs its actual read and write, at an
   explicitly bounded index, producing exactly refreshAfter.
4. tlb_get_pbmt of a source entry returns PBMT_PMA from the derived
   PbmtZero word fact, through its actual Sail program.

These are register-only plan obligations, not WPs and not replacement
interpreters. The footprint is the existing single full TLB cell; all
other physical register values remain unconstrained. No new camera or
resource capability is introduced. A cached-entry permission test and
A/D update result are not assumed to succeed.

The source shared snapshot wrapper is
`∃ tree, pure(Coherent 0 tree tlb) * snapshot tree`. KptShare.tlb_res_pt
additionally owns full SATP/TLB, Sv39 mode/ASID-zero/root facts, PMP,
shared KPT and publication credentials. Those are native resources and
are deliberately not replaced by this pure relation or implemented in
this slice. Canonical transport will be its usable prerequisite.

The complete two-tree source relation at PtTree.v:2000–2111 is a separate
future slice: each occupied hash slot has CacheOf in either the previous
or current tree. It is not required for fixed shared-table snapshot
coherence, and is not merged into Coherent here. SATP-switch windows must
use that disjunction, including side-specific canonical transfer, fill and
writeback; a hit refresh retains its installing provenance even if that
was the previous table. No current-only theorem here is claimed to cover
those windows.

Full translate_TLB_hit remains open. Its real code checks permission
first, may return the exact error, otherwise invokes update_and_write_pte
at ent.pteAddr and the decoded level. Only an Ok(Some word) response
refreshes the TLB; Ok(None) and Err do not. Its returned PPN/PBMT are read
from the original entry. This slice proves the algebra and register
operations needed to preserve coherence when those actual branches are
later discharged; it does not take a successful update or hit as an oracle.

The implementation discharges the universal 64-entry/collision laws and
four actual plans. Set-leaf preservation uses the proved canonical-tree
equality directly, avoiding redundant updated-leaf premises. The finite
level getter is reduced with the actual IntRange loop equations; no native
decision procedure is used. A complete physical-origin, type, opaque-body
and constructor audit accompanies the freeze before independent review.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
