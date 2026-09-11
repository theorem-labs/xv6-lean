# Kernel leaf words and actual validator

Frozen five modules: KptLeafDefs/Spec/WordProofs/Plan/Link. Both complete
WordSpec and PlanSpec are implemented and exported by their native links.
Coordinator definitions/signatures received independent source review before
implementation. Source: KptPt428–454/706–795, Pt4kWalk26 and actual generated
VmemPte invalid/permission functions plus Vmem.check_leaf_pte.

The two source permission classes use exact RX0x0b/RW0x07 base flags with
arbitrary A/D bits. Words concatenate symbolic44-bit PPN with ten flags and
zero-extend to64. Kernel proofs establish generated flag/PPN/extension
extraction, leaf classification, exact A/D replacement and canonical word.
No physical page number or mapping is chosen by the proof.

The permission contract supports exactly fetch, Data load/store and Data
AMOSWAP with arbitrary aq/rl. Allows admits fetch only for RX, loads for
both, and stores/swaps only for RW. The actual permission program equals
pure success for arbitrary MXR/SUM. No store-to-text permission is claimed.

The invalid-PTE plan retains five eager register reads: menvcfg, misa,
misa, menvcfg, misa. Every result is independently universal. The complete
level0 Sv39 validator composes that plan, real permission program and the
two remaining Svnapot/PBMTE reads, returning precisely the original PPN,
PBMT_PMA and unit. All seven reads remain actual free events. Empty
footprints follow from universal read proofs, not an erased interpreter or
whole-register ownership. No program=pure equality is claimed for either
of these reading validators. Existing RegisterPlan folding supplies their
native WP use.

Validation: full Link build passed434 jobs (Plan7.2s, Link894ms). Fresh
physical-origin audit checked292 declarations in all five modules, including
private helpers, transitive types, opaque bodies and constructors; only
propext, Classical.choice and Quot.sound; zero exclusions or unsafe/partial
logical dependencies. Evidence: /tmp/xv6-lean-research/KptLeafAudit.lean,
kpt-leaf-build.log and kpt-leaf-audit.log. Earlier elaboration failures were
fixed before the successful build. Generated dependent-width rewrites use
erw, retaining kernel equality; final ExceptT/free callbacks are composed
explicitly. Finite bit cases use kernel reductions, without native_decide.

This proves the concrete kernel leaf validator. The shared KPT invariant,
three-level hardware walk, TLB behavior and full source supervisor function
regime remain separate. All six whole-xv6 theorem roots remain open.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
