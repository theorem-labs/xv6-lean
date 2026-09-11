# Actual direct-slot Sv39 walk

Seven frozen modules: Defs, Spec, Pure, Factor, NodeProofs, Proofs and Link.
The independently stated Spec.walk is fully implemented by wp_walk/nativeSpec.
The actual generated pt_walk39 begins at level2 and returns the actual
PTW_Output with leaf PPN, physical PTE address, level0, PBMT_PMA, leaf word
and unchanged global flag. No alternative executable walk is introduced.

Path contains four arbitrary 44-bit PPNs. The upper words are exact valid
pointers with flags1 and zero RSW; the leaf is the existing rx/rw kernel
word with arbitrary A/D bits. Fetch/load/store/AMO-swap use the exact source
permission classifier. Config supplies checked physical supervisor access
at all three computed addresses on the same four fractional register cells.
All pointer/address/canonical consequences are proved from these definitions.
No page alignment, read result, per-node WP or continuation preservation
oracle is supplied by the caller.

Each of three ordinary memory events uses the existing native pinned-slot
WP and permits every legal TSO view. Exact nonleaf reconstruction identifies
the two pointer words; canonical equality derives the leaf's A/D variant.
The contract starts with arbitrary physical byte functions and independent
fractions for the three slots, retaining all original floor/anchor assertions.
It returns all three unchanged slot predicates, the four cells, publication
credential, unchanged incoming reservation and all three chosen-view receipts.
The genuine final continuation has exactly three memory guards.

Factor proves the complete generated control tree independently at each
level: failed read, invalid/recursive choice and leaf-validator failure are
retained before the native rules specialize them. Each interior validity
check executes five universally quantified register reads. Level0 first
executes the same five reads, then check_leaf_pte repeats validity and reads
two extension controls: twelve reads at the leaf. Including three checked
memory prefixes, the success path has 37 register reads and three ordinary
memory reads. Universal reads require no extra owned control cells.

Source and implementation review caught a generated implicit-width coercion
in the new factor before it compiled: PPN_of_PTE is explicitly instantiated
at64, and every factor is proved against the actual generated tree. No model
or dependency change was made. Restricted-transparency Iris aliases are
normalized by kernel-checked change/ieval; no axiom or execution shortcut is
used. Pure bitvector/address proofs use kernel reduction and arithmetic.

This is the directly owned concrete-pointer path, not full shared KPT.
The source permits valid raw upper G/RSW bits; the subsequent shared-tree
layer must retain them and accumulate G. The current path has G=0 in all
three words and therefore preserves the incoming global flag. No invariant
is kept open across events. Shared per-event access, boot pin publication,
TLB hit/miss/fill/refresh, generalized raw-pointer traversal, supervisor
translation and virtual mycpu remain subsequent source integration work.
No A/D write occurs inside pt_walk; that is the separate actual TLB/update
path. No whole-xv6 root is closed by these component theorems.

Validation: final Link build passed633 jobs, factor2.5s, node1.0s,
composition0.9s, Link0.8s. Fresh complete physical-origin audit passed all108
logical declarations across seven files, including private/generated roots,
types, opaque bodies and datatype constructors; standard three foundational
axioms only, zero exclusions or unsafe/partial logical dependencies.
Evidence: /tmp/xv6-lean-research/Sv39WalkAudit.lean,
sv39-walk-final-build.log and sv39-walk-audit.log.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
