# Full physical heap and metadata

`Heap{Defs,Spec,Proofs,Registry,Link}.lean` integrates the complete native Iris
`genHeapInterp` over `PhysicalAddress = BitVec 64`, preserving the existing TSO
value camera. Source references use xv6iris arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476` and native Iris
`728a17140939e49af9236f7cb0d037da9ec52435`.

The source `RiscvPtsto.v:413–417` stores `gen_heapGpreS` capacity separately from
era names. `era_memGS_of` at lines 533–535 reconstructs the heap instance from
its value and metadata names; `era_interp` at line 2152 owns the full heap.
Physical-byte validity and update use it at lines 2593–2595 and 2651–2654.
`Iris/BI/Lib/GenHeap.lean` supplies the actual corresponding Lean predicates,
resource algebras, metadata laws, and finite-map initialization proofs.

| Resource or source operation | Lean interface in `MachCSL.Logic.Heap` |
| --- | --- |
| `gen_heapGpreS`, `era_memGS_of` | Explicit `Capacity.preS`, `Capacity.native`, and two-name `Names` |
| `gen_heap_interp` | `interp`, exactly native `Iris.genHeapInterp` |
| Byte `pointsto`, physical `pointsto` | `pointsto`, `physicalPointsto`; their equalities to the existing ledger predicates are proved by `rfl` |
| `meta_token`, `meta` | `token`, `metadata`, exactly native predicates |
| `gen_heap_init_names` | `allocate`, returning full heap interpretation, every full byte fragment, and every top-mask metadata token |
| `gen_heap_valid`, `gen_heap_update`, `gen_heap_alloc` | `valid`, `update`, `allocateCell` |
| `meta_token_union`, `meta_token_difference`, `meta_set`, `meta_agree` | `token_union`, `token_difference`, `metadata_set`, `metadata_agree` |
| Metadata integration with existing TSO allocation | `attachMetadata`, preserving the existing byte authority's name |

There are exactly two added metadata cameras: the physical-address-to-ghost-name
indirection map at slot 13 and native `MetaUR` reservation maps at slot 14.
`registry` extends `Disk.registry`; `registry_old` preserves slots 0–12, and all
previous capabilities are explicitly derived. `registryCapacity.ledger` is the
same `ledgerCapacity`, and `byte_slot_zero` proves the heap value camera remains
slot 0. In particular, no second byte camera or altered points-to predicate is
introduced. Metadata ghost names and byte ghost names remain explicit runtime
data, separately allocated from these capacity certificates.

`attachMetadata` upgrades an **existing** full `Tso.byteAuth` at its existing
name. A private finite-map induction allocates only the metadata indirection
authority and one native reservation token per present key. It then combines
these resources with the caller's value authority into full `genHeapInterp`.
Existing client byte and timestamp fragments frame through this basic update;
all newly allocated metadata tokens are returned. There is no throwaway second
value map and no conversion of writable bytes to read-only ownership.

Physical addresses are finite. The inspected native `genHeapPreS` requires only
`LawfulFiniteMap`, and the relevant allocation proofs require `DecidableEq`.
They do not require `InfiniteType` or fresh physical addresses outside the
finite domain. `allocateCell` retains the exact explicit absent-key premise.
Fresh ghost names come from native ghost allocation, whose name domain is a
separate resource. No Iris fork was needed.

`HeapSpec` is independent of proof implementations and includes allocation,
metadata attachment, lookup/update/new-cell rules, token splitting, metadata
setting and agreement. `heapSpec` proves the contract; `registryHeapSpec` links
it to explicit registry capacity. This is a completed physical-heap component,
not a complete xv6 era interpretation or machine safety proof. Composition
with other era resources, ownership step preservation, instruction rules and
adequacy are separate tasks. The existing finite-map bridge does not itself
check a Rocq-to-Lean representation translation.

Validation: `python3 tools/lake.py build MachCSL.Logic.HeapLink` passes 362 jobs.
A module-origin audit passes all 164 declarations in the five modules, including
the private metadata allocation helper, and permits only `propext`,
`Classical.choice`, and `Quot.sound`. Exported allocation, attachment,
absent-key allocation, byte identity, and concrete linked-contract types were
inspected. The audit source and log are `/tmp/xv6-lean-research/HeapAudit.lean`
and `/tmp/xv6-lean-research/heap-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
