# General raw-pointer Sv39 walk

All six modules (Defs, Spec, Factor, NodeProofs, Proofs, Link) are frozen.
The final build passed 647 jobs: Factor 897ms, NodeProofs 891ms, Proofs
1.1s and Link 832ms. The geometry definition resides in Defs; the
coordinator-requested layout move changed no theorem or contract. `actual` constructs both approved native contracts;
`nativeSpec` exports the complete implementation without additional
execution or resource-access specifications.

The source boundary is PtTree.v:90–139,435–501, CommonWalk.v:38–58,
145–240,355–416,509–563,652–795 and KptPt.v:435–457,706–794 at xv6iris
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. The actual generated call is
Vmem.lean:365–411 at model23dcf8fd923eb8a1958795393d2975632aa940b2.
See docs/design/sv39-tree-walk-boundary.md for precise source mapping and
scope; whole-model Lean/Rocq correspondence remains separate.

`pointer_next` proves the actual recursive branch for arbitrary pointer
words, preserving G and the full 64-bit PTE's PPN projection. `address_same`
bridges the existing walk geometry to source PtTree geometry at every
natural level. `mapped_pointers` extracts the exact upper validity and
pointer facts from actual PtTree.Maps, without extra G/RSW restrictions.

`wp_pointer` performs the actual ordinary read and derives exact raw-word
identity from the nonleaf pin family. It invokes the existing native
raw-pointer validation plan, which covers all five eager register reads
universally. The recursive residual uses the actual nextBase and accumulated
G bit. The proof reuses the checked full generated node factor, preserving
all error, leaf and callback definitions.

`wp_walk` composes two such nodes and the existing kernel-leaf node. The
old path record supplies geometry only; its flag-one pointer representation
is never used for either upper slot. `output_eq` retains the public exact
PtTree.globalAfter formula, including the final leaf bit. The kernel leaf
G bit is proved zero for every PPN, permission and A/D pair.

The full walk starts at tree.base and takes the actual PtTree.Maps premise.
It returns all three original directly owned pinned slots, the publication
credential, the four-cell fractional register footprint, the incoming
reservation and all three actual selected-view receipts. Its leaf A/D
pair remains universally independent of the tree reference and current
physical byte functions. There is one guard per real ordinary read and
only the genuine final residual-program WP continuation. There is no
read-value, validation-plan, callback or memory-success oracle.

A fresh physical-origin audit checked all 49 declarations in the six
modules, including types, full opaque bodies and inductive constructors.
Only propext, Classical.choice and Quot.sound occur; there are no
unsafe/partial semantic dependencies and zero exclusions. No custom axiom,
sorry, native_decide or bv_decide is used. Independent peer review remains
requested before publication.

No new camera, shared-invariant opening, publication, TLB coherence,
A/D update, or translated function theorem is claimed. This is direct
slot ownership, so it does not hold a future shared KPT invariant open
across the three reads. Existing frozen modules and umbrella imports
were not changed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
