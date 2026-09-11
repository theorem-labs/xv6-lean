# Native Sv39 walk with source raw pointer words

The owned prefix is `Xv6/Kernel/Sv39TreeWalk`. All six modules (Defs, Spec,
Factor, NodeProofs, Proofs, Link) are now implemented and frozen. The full
build passed 647 jobs and the complete native Spec is constructed. The
approved interface is unchanged. Existing Sv39Walk, Sv39Miss, PtTree and
pinned memory modules are unchanged.

The sources are xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`:
PtTree.v:90–139,435–501 for semantic validity, raw pointer classification,
addresses and Maps; CommonWalk.v:38–58,145–240,355–416,509–563,652–795
for actual node control, accumulated global bits and the native per-read
boundary; KptPt.v:435–457,706–794 for kernel leaf permission classes.
The shared integration context is docs/design/shared-kpt-boundary.md.
The actual generated program is models/riscv/LeanPaperStock/Vmem.lean:
365–411 at model pin `23dcf8fd923eb8a1958795393d2975632aa940b2`.
The existing checked Sv39WalkFactor is a reusable decomposition of that
program, including its full response branches. These are source mappings,
not a checked equivalence of the Lean and Rocq generated models.

The current Sv39Walk fixes upper words to a PPN concatenated with flag one.
The new interface takes arbitrary 64-bit p2 and p1 words and an actual
`PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission referenceA referenceD)`
premise. It imposes no additional G/RSW restriction, page-allocation layout,
child identity or distinct-pages premise. The program starts at
`PtTree.base tree`; it does not execute the pure tree's children functions.
Maps supplies the source tie between raw pointer PPNs and those children.

The three physical addresses are exactly `PtTree.addr2 tree vpn`,
`PtTree.addr1 p2 vpn` and `PtTree.addr0 p1 vpn`. In particular, both lower
addresses extract `PPN_of_PTE (k_pte_size := 64)` from the full raw pointer,
then concatenate the 44-bit PPN, nine-bit VPN slice and three zeros before
zero-extending to 64 bits. No masked pointer representative is substituted.
Config supplies the existing concrete physical PTE-read configuration at
each of those addresses: actual eight-byte RAM/alignment, TOR/PMA grant and
HTIF prerequisites. These are the direct-owned-slot boundary, not an
assumed page-tree ownership or shared accessor theorem.

The native inputs are one four-cell PMA/PMP/HTIF footprint with arbitrary
permitted fractions, the generation certificate, the existing publication
credential, three actual eight-byte pinned slots and the incoming reservation
fragment. The slot reference is the exact raw upper word at levels two and
one. Level zero uses the canonical kernel-permission word with A/D cleared.
All three current byte functions and fractions are independent parameters;
the existing slot resources supply their actual byte/pin ownership, floors,
bounds and anchors. The tree's reference A/D bits and the actual physical
bytes are not required to match. The credential retains both original boot
and nonboot arms, with no added top-view receipt assumption.

`Spec.pointer` is a reusable one-node rule. Its premises are the exact
`PtTree.Valid raw` and `PtTree.Pointer raw`, a level in {1,2}, the concrete
read configuration and native resources. It performs the actual read and
validation, then exposes the actual recursive `pt_walk` continuation at
`PtTree.nextBase raw`, level minus one, and
`global || PtTree.globalBit raw`. It returns the same slot, four cells,
credential and reservation, plus the actual selected-view receipt, under
one memory-event guard. It has no read-response premise or caller-supplied
register-plan/memory-success callback.

`Spec.walk` takes the actual Maps premise and supported/allowed kernel
access. The final continuation is guarded three times, once per real
ordinary PTE-read event. It receives all original slots, cells, credential,
reservation and all three selected-view receipts. Its A/D parameters are
universally quantified and independent of both referenceA/referenceD and
the flat byte functions. The actual output contains the returned leaf word,
its exact physical address, level zero, PPN and PBMT_PMA. Its global field is
`PtTree.globalAfter initial p2 p1 returnedLeaf`: all three source OR steps
remain visible even though the kernel leaf family itself has G=0.
The only WP premise is this genuine residual-program continuation.

Do not conclude that `Maps tree vpn ... returnedLeaf` holds when the tree's
reference A/D bits differ: the description has fixed entries. Canonical
leaf agreement is the relevant relationship. The read-only walk changes no
physical table word or pure tree description. Any later setLeaf update or
shared snapshot transport belongs to its own proven access layer.

Implementation reuses the frozen generic `Sv39Walk.node_eq`,
`afterRead`, `afterInvalid` and `afterLeaf` factors, not its flag-one pointer
WP. `pointer_next` proves the raw recursive equation retaining G. The native
node derives its empty-footprint validation plan from
`PtTree.nativePointerSpec` and folds all five eager validation-register
reads universally. The actual SupervisorPteRead rule obtains exact raw upper words from
their nonleaf pin families. No hypothetical zero register file or fixed hardware value
is used for the native execution.

The leaf reuses the existing kernel-leaf node rule through a geometry-only
Sv39Walk.Path (root, nextBase p2, nextBase p1, leaf PPN). `output_eq` transports its output to the explicit raw-pointer globalAfter
formula, preserving the independently selected A/D bits. Maps supplies both upper
validity/classification pairs; it is not replaced by a validation oracle.

The generated successful route has three memory events and 37 register
reads: five physical-prefix reads per slot, five validity reads at each
upper node, and twelve validity/leaf-check reads at level zero. The final
level includes the actual repeated validity check. The owned footprint
remains four cells because the other reads are proved for every response.
These counts are the intended path accounting, not a replacement for the
kernel-checked factor and native folds.

All actual error branches remain in the generated program and factors:
a failed PTE wrapper yields PTW_No_Access; invalid/nonleaf-at-zero and
permission failures reach the actual check_leaf_pte branches. The resource
proof and semantic Maps/kernel-permission premises must discharge those
branches for this successful direct-slot contract. Actual start/step/fail/
success callbacks remain those of the pinned generated model; the existing
factor equality reduces their actual definitions, rather than assuming
new event-free callbacks. No A/D update, exclusive reread, conditional write
or TLB read/fill occurs inside pt_walk. Those remain distinct later calls.

This slice allocates no camera and no invariant. In particular, it cannot
hold a future shared KPT invariant open over three memory events or serve
as an invariant restoration callback. Shared publication, per-event access,
TLB provenance/coherence, boot initialization and translated mycpu remain
separate work. Both approved contracts are implemented. A fresh physical-origin audit
checked all 49 declarations across the six modules, traversing types,
opaque bodies with `allowOpaque := true` and inductive constructors. Only
propext, Classical.choice and Quot.sound occur; there are no unsafe/partial
semantic dependencies and zero exclusions. Independent source/proof review
remains requested before publication.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
