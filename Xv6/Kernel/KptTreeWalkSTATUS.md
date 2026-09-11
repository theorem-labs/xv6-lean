# Shared three-level walk

All six modules Defs, Spec, PteProofs, NodeProofs, Proofs and Link compile.
`actual` implements both approved native contracts: one selected `read_pte`
wrapper and the complete actual `pt_walk 39 ... Supervisor ... 2` call.
`nativeSpec` and `registrySpec` discharge all internal register/control and
shared-event dependencies. The approved Defs/Spec signatures are unchanged.

The register footprint is exactly the existing four fractional control cells:
`pma_regions`, `pmpcfg_n`, `pmpaddr_n`, and `htif_tohost_base`. It is reused
sequentially with the same register file and shares. `Config` is the frozen
Sv39TreeWalk physical configuration: exact TOR/range/alignment, actual PMA
match and PTE grant, and disabled HTIF, at each of the three path addresses.
It assumes no memory-read outcome or prebuilt control plan. Raw-pointer and
leaf validation use the existing universally checked register plans, so they
require no additional owned architectural registers.

`clients` contains only the shared invariant, canonical snapshot, exact
publication bound and matching boot/view credential. All use the same
machine-derived capacities. No physical slots, byte arrays, slot fractions
or tree reconstruction callbacks appear in either public precondition.
The original reservation is separately owned and returned unchanged.

The proved selected PTE contract retains the complete Maps path and an actual
Fin 3 level. It invokes the frozen register-only PTE prefix factor, then the
actual KptReadEvent ordinary event, then its checked response tail. The
source plain access metadata is retained. The result is canonically equal
to the reference, and is exactly the complete raw reference when it is a
nonleaf. This wrapper exposes one guard and one actual view receipt.

The whole walk composes levels 2, 1 and 0. Its pure premise supplies an
arbitrary source-valid raw upper path and a reference kernel leaf variant.
The upper words retain all G/RSW bits and the 64-bit PPN field projection;
neither is replaced by a flag-one word. The actual first node begins at
`tree.base`, exactly as the existing tree walk program does. Shared snapshot
agreement ties this base to the invariant publication; no separate logical
tree is executed.

After each read, the shared invariant has already been closed by the native
event. Between reads, arbitrary permitted machine interference remains
possible. The leaf returned by the third read is selected at that actual
view; its A/D pair is independent of the reference pair. Source permission
and supported-access premises discharge the actual leaf validator. The
result retains actual PPN, leaf word, `pteAddr`, level zero, PBMT_PMA and
`PtTree.globalAfter global p2 p1 leaf`. All three native receipts are returned
in read order, with no invented ordering or global-top assertion. Exactly
three guards precede the genuine final residual-program continuation.

Implemented proof decomposition within this prefix:

1. `fold_boundary` folds the already checked `SupervisorPteRead.program_boundary` using the
   four-cell native RegisterPlan fold. Its actual read event uses
   `KptReadEvent.nativeSpec`, retaining both checked success and error tails.
2. `wp_pointer` factors each actual `pt_walk` node with `Sv39Walk.node_eq`. For upper
   nodes it derives exact words from ReadFact and Maps, then reuses
   `PtTree.nativePointerSpec.validation_plan` and
   `Sv39TreeWalk.pointer_next`, including eager validation reads.
3. `wp_leaf` at level zero derives the leaf A/D variant from canonical equality and
   reuses the actual `Sv39Walk.leaf_plan`, preserving the full leaf output.
4. `wp_walk` composes the three proved nodes; `nativeSpec` and `registrySpec`
   discharge component specs. No camera is added.

Source map, pinned `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`:

- `PtTree.v:90–139,435–501`: raw semantic validity, leaf classification,
  exact three-level address calculation and full Maps path.
- `HartSKpt.v:125–205,253–309`: pinned all-view ordinary reads, exact
  upper words and canonical leaf, with full invariant closure per event.
- `HartSKpt.v:603–737,1144–1189`: actual PTE wrapper seams and composition
  of two exact upper reads with the predicate-indexed leaf read.
- Generated `LeanPaperStock/Vmem.lean:365–411`: actual pt_walk recursion,
  ordinary read, full response cases, validation, G accumulation and leaf
  output. Existing node factor preserves the error and callback branches.

This checkpoint ends before A/D reread/conditional commit, TLB miss/hit or
coherence, translateAddr, virtual memory-resource bridges, actual boot
publication and translated mycpu. It does not turn a direct-slot theorem
into a shared theorem by assuming a resource-access oracle.

Validation: the final `python3 tools/lake.py build Xv6.Kernel.KptTreeWalkLink`
passed all 755 jobs. PteProofs compiled in 1.2 s, NodeProofs in 1.1 s,
Proofs in 1.1 s, and Link in 948 ms. The complete physical-origin audit
is `/tmp/xv6-lean-research/KptTreeWalkOwnerAudit.lean`; raw build and audit
logs are `kpt-tree-walk-owner-build.log` and `kpt-tree-walk-owner-audit.log`
in the same directory. Every declaration, including private helper proofs,
is checked through types, opaque bodies and inductive constructors, with
zero exclusions. All 47 physical declarations passed with only `propext`,
`Classical.choice`, and `Quot.sound`, and no unsafe or partial dependencies.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
