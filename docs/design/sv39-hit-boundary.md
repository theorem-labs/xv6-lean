# Supervisor TLB-hit boundary

The owned prefix is Xv6/Kernel/Sv39Hit. All six modules compile (496 jobs).
The coordinator approved the actual Defs/Spec checkpoint before proofs.
Link now constructs all nine FactorSpec contracts, two PlanSpec contracts
and two native Spec contracts. The signatures remain unchanged. Existing
frozen modules and umbrellas are unchanged.

Source inventory read before choosing the boundary:

- PtTree.v:2200–2410: stored-entry getters, matching and denied/no-update hit.
- PtTreeAdue.v:2250–2445: atomic reread/check/write and reread-only refresh hits.
- KptTree.v:835–1005: resident hit routing through unchanged, refresh and write
  outcomes, including stale cached A/D versus current physical A/D.
- CommonWalk.v:795–806 and PtTree.v:1693–1791,1954–1991: exact installing entry
  and single-tree cache provenance, already reviewed as TlbCoherence.
- Actual generated Vmem.lean:446–474 translate_TLB_hit, VmemTlb getters and
  write_TLB, VmemPte.check_PTE_permission, existing KptLeaf and
  SupervisorPteAD program/afterGate/afterRead/afterCheck/afterWrite definitions.

Artifact pin fa7f0a01c4b40489fac8ad303f079c2dfc7a1476 and model source pin
23dcf8fd923eb8a1958795393d2975632aa940b2 remain unchanged. This mapping does
not assert cross-backend equivalence: generated eager register reads are
retained even where the Rocq sequential proof describes pure checks.

`program` is actual translate_TLB_hit39 in Supervisor mode, with arbitrary
ASID, VPN, index, stored entry, access, MXR and SUM. `permission` is the real
cached-word check. `afterPermission` preserves its failure and success arms;
on success it invokes the actual update_and_write_pte at the original
entry's pteAddr and level. `afterUpdate` preserves every Err, Ok(None) and
Ok(Some word) result. Only Some calls actual write_TLB with tlb_set_pte.
Every successful hit returns PPN and PBMT from the ORIGINAL entry, as the
model does; it does not use the freshly supplied word to recompute them.
Raw factors have no permission-success or leaf-validity premise.

The source walk-entry specialization uses TlbCoherence.entry verbatim. Its
address is PtTree.addr0 of the installing p1 and origin VPN; current SATP/root
never replaces it. Its level is proved zero, without an assumed getter result.
The kernel specialization uses existing KptLeaf RX/RW words and its four
supported access classes with Allows. The existing checked permission proof
is applied only in this specialization. A separate denied contract applies
to an exact failure equation of the actual permission computation.

`head` examines the actual cached update_PTE_Bits result. None is immediately
pure and reads no MENVCFG. Some performs the exact existing AD gate, whose
checked model normalization is one MENVCFG read and its ADUE bit. It does
not assume the bit true. `headValue` is the corresponding pure selection.
The native head rule consumes the two-cell footprint (fractional MENVCFG,
full TLB), folds just that real prefix, and returns the SAME cells to a
continuation requiring WP of `remainder`.

The remainder has three exact behaviors: cached -> afterUpdate(Ok None),
disabled -> the real PTW_PTE_Needs_Update error, enabled -> actual
read_pte_exclusive at the installing address, followed by existing
SupervisorPteAD.afterRead and the hit afterUpdate. This retains all read
errors, revalidation errors, physical-word update decisions, conditional
write errors and the Ok(false) internal-error terminal computation. The
old cached word merely triggers rereading; the physical reread word determines
what gets written. Full check_leaf_pte stays in afterRead, including all
its eager feature-register reads. No memory event or revalidation call is
replaced by a pure success or an uninterpreted atomic callback.

The enabled remainder WP is deliberately the remaining proof obligation.
Its physical registers, reservations, shared leaf ownership, publication
credentials, conditional-write receipts and memory-event guards must be
provided by the later actual shared A/D rule. This boundary adds no extra
terminal guard, no memory success oracle and no replacement invariant. It
introduces no camera, allocation, boot constructor or Initial dependency.
The existing model has conditional exclusive memory events; no claim is
made that the entire read/check/write sequence becomes one atomic node.

The resume plan and native rule quantify over EVERY actual UpdateResult.
Given PBMT zero for the original entry, they return the exact result and
register file. They change only the full TLB cell on Some, retaining the
MENVCFG share. The native rule is intended to be applied after the actual
memory remainder has supplied its result; it does not assume that result
is reachable or successful. The index bound is explicit for refresh.
Its plan preserves the real TLB read and write; unlike miss fill there is
no callback read on this path.

`UpdateVariant` requires an A/D variant only for Ok(Some word), and is True
for Err/Ok(None). The pure coherence-resume law uses this exact conditional
premise plus actual slot membership and the existing single-tree Coherent
relation to preserve the complete TLB. This premise must later be derived
from the shared physical snapshot/update, not asserted as a consequence of
arbitrary update success. Stale A/D admits both directions and does not
restrict the foreign-tag/hash-collision behavior of Coherent. The head
and raw factor do not silently infer tag matching: lookup and cache origin
are separate prerequisites of a caller routing an actual TLB hit.

Exact factor equations and register plans are proved, and the native folds
use the actual RegisterPlan implementation. Fresh physical-origin audit
covers all 80 declarations across six modules, traversing types, opaque
bodies and datatype constructors: only propext/Classical.choice/Quot.sound,
no unsafe/partial logical dependency and zero exclusions. Seven additional
kernel checks cover cached/no-gate, needs-gate, disabled error, original PPN
under a different response word, None/error unchanged registers and false
conditional-write not-success. Full translate_TLB_hit shared WP, two-tree
SATP-switch coherence and translated mycpu remain later work.
The native residual cannot be advertised as full hit closure before its
actual enabled-memory WP is discharged.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
