# Raw page-table pure foundation

The complete approved pure slice is implemented and linked: `PtTree.nativeSpec`
proves all 15 tree contracts; `PtTree.nativePointerSpec` proves the four raw
pointer contracts. This is the first implementation checkpoint of
[the shared KPT design](../../../docs/design/shared-kpt-boundary.md).

The inert total-function tree retains arbitrary raw PTE words and arbitrary
children, including children below level zero. `Maps` preserves the exact
three-level source path; `Blocks` has exactly the three invalid-stop cases.
Selected-leaf updates preserve other VPNs and blocked paths. Canonicalization
changes only level-zero A/D bits, preserves mappings in both directions, and
is unchanged by an A/D update to a mapped leaf. No valid-level-zero-pointer
case or stronger recursive well-formedness condition has been added.

`Outcome` requires a finite execution of the actual generated validator for
every dependent register file. Its natural fuel is existential in the
architectural predicate. `validation_eq` proves that the generated function
performs five eager reads, in order: `menvcfg`, `misa`, `misa`, `menvcfg`,
`misa`. `validation_run` proves a six-fuel witness for the complete operation;
`registerRun_result_unique` proves uniqueness across arbitrary successful
fuel bounds. The Boolean transcription `invalidValue` is connected by the
checked generated-program equation, not assumed to be the validator.

From semantic `Valid` and `Pointer`, `pointer_fields` derives extension bits
zero, V=1, and A/D/U=0. `pointer_validation_plan` retains all five actual reads
as independent universal reads and returns false with unchanged registers.
It uses an empty ownership footprint because the derived PTE constraints make
the outcome independent of every read value. G, both low RSW bits, and PPN
remain arbitrary; `nextBase` explicitly sets `k_pte_size := 64`. `global_setAD`
preserves the actual G bit. Leaf validity is transported across A/D changes
by equality of the full generated validation programs, with the leaf premise
retained because A/D bits are reserved on pointers.

Source mapping (paper pin `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`):

| Lean symbols | Pinned source |
| --- | --- |
| `Tree`, projections | `PtreeType.v:20–30` |
| `Valid`, `Invalid`, `Pointer`, `Leaf`, leaf extras | `PtTree.v:90–139` |
| `pointer_ext_zero`, raw-pointer fields | `PtTree.v:332–358`; generated `VmemPte.pte_is_invalid` |
| `index`, `addr2/1/0`, `Maps`, `Blocks` | `PtTree.v:435–500` |
| `maps_det`, `valid_invalid`, `maps_blocks_excl` | `PtTree.v:503–553` |
| updates, `index_injective`, three `set_leaf_*` laws | `PtTree.v:561–805` |
| `set_ad_valid_leaf`, canonicalization laws | `PtTree.v:1838–1953` |
| `maps_across` | Pure path transfer used by `tlb_ok_pt_canon`, `PtTree.v:1958–1981`; no TLB theorem is claimed here |

`PtTreeExamples` checks non-vacuity with a pointer carrying G and both RSW
bits, valid leaf words with distinct A/D bits, and the all-state invalid zero
word. These are ordinary kernel proofs of actual validation results.

This layer allocates no ghost state and claims no shared ownership or native
translation WP. Recursive tiered ownership, map/tree agreement cameras,
one-shot publication and log bounds, boot context-to-pin conversion, native
per-event shared accessors, generalized raw-pointer walking, TLB coherence,
and translated `mycpu` remain subsequent work. The semantic predicates are
Lean counterparts of the source `exec` predicates; formal Rocq/Lean semantic
correspondence is not claimed. Slots 45–47 remain reserved for the proposed
KPT camera layer, after the frozen `SupervisorBits` slot 44.

Validation commands and evidence:

- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.PtTreeExamples`
  passed all 339 jobs (final example module 783 ms).
- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/PtTreeOwnerAudit.lean`
- The owner audit selects every declaration by physical source module,
  traverses types, opaque theorem bodies (`allowOpaque := true`) and inductive
  constructors, and rejects any axiom beyond `propext`, `Classical.choice`,
  `Quot.sound`, or any unsafe/partial dependency. All 640 physical declarations
  in 11 modules passed, with zero exclusions. Raw output is
  `/tmp/xv6-lean-research/pt-tree-owner-audit.log`.
- `git diff --check` and a direct trailing-whitespace/final-newline check of
  every owned file pass (the direct check also covers new untracked files).

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
