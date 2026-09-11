# Independent TLB coherence review

PASS for the six frozen TlbCoherence modules, STATUS and design. All twenty
pure contracts and all four actual register plans match their stated source
boundary. No implementation correction is required.

I read the complete six-module implementation and compared it to pinned
`iris/PtTree.v:1680–2111,2174–2541`, `CommonWalk.v:795–810`, and
`KptShare.v:153–220`, plus the complete generated `VmemTlb.lean` and the
hit/miss control in `Vmem.lean:446–505`. I also checked the reused PtTree
carrier/classification definitions, Sv39Tlb fill proof and RegisterPlan
constructors. Artifact pin: fa7f0a01c4b40489fac8ad303f079c2dfc7a1476;
model pin: 23dcf8fd923eb8a1958795393d2975632aa940b2.

CacheOf retains an existential installing VPN and only equates hash indices;
it never substitutes query equality before the actual tag test. Coherent
quantifies through this hash as the source does. The checked optional-vector
access adds an outer Some for the index; the hash bound and surjectivity
laws establish coverage of every one of the 64 physical slots. Stored ASID
is fixed by the source relation, whereas requested ASID remains arbitrary.
The matcher law includes the accumulated global-bit exception and sign-extended
45-bit tag. The complete originating level-one PTE supplies pteAddr; a later
tree base cannot replace it.

Variant permits both clearing and setting either A/D bit. Canonical transport
uses the source level-zero-only tree canonicalization and preserves raw upper
words and origin geometry. Cached validity, leafness, NAPOT absence and PBMT
zero follow from Maps. The set-leaf proofs remove only redundant source
classification premises, deriving their consequences from Maps and A/D
stability; they do not canonicalize invalid nonleaf words into valid ones.
The refresh proof uses the actual resident entry, retains its origin even
under a collision, and proves that changing only pte agrees with rebuilding
an A/D-variant entry. Its PPN and accumulated global flag are unchanged.
Lookup provenance follows only after the actual match succeeds. The blocked
lookup theorem therefore rejects foreign entries sharing the same hash slot.

The four plans use the actual generated computations: lookup has one read;
fill has read/write/read, retaining the universal callback read; refresh
has read/write; PBMT extraction follows the genuine Sail program with the
explicit PbmtZero premise. The footprint is the existing full TLB cell;
readAny quantifies its returned value rather than deleting the event. The
refresh plan keeps its source index bound even though the generic vector
update proof does not need it. The level getter proof reduces the actual
bounded IntRange loop, and the PPN getter retains the source zero level mask.
Link constructs both Specs from checked proofs, with no successful-translation
oracle or new camera.

Ten independent kernel checks passed: an actual 3/67 hash collision, collision
miss, own-tag hit, foreign-ASID miss, upper-pointer global-bit acceptance,
both directions of stale A/D variation, retained refresh origin address,
retained refresh PPN and a negative sign-extended VPN tag. These checks are
additional concrete sensitivity evidence; the main contracts remain universal.

A fresh build completed successfully (449 jobs). A fresh audit checked all
101 declarations by physical origin, including private/generated declarations,
and traversed their types, opaque bodies and datatype constructors. Only
propext/Classical.choice/Quot.sound occur; there is no unsafe/partial semantic
dependency and there are zero excluded roots. Audit and check evidence:

- /tmp/xv6-lean-research/TlbCoherencePeerAudit.lean and tlb-coherence-peer-audit.log
- /tmp/xv6-lean-research/TlbCoherencePeerChecks.lean and tlb-coherence-peer-checks.log
- /tmp/xv6-lean-research/tlb-coherence-peer-build.log

This review approves pure single-tree provenance and four register plans.
It does not establish the separate two-tree SATP-switch relation, native
shared-tree snapshot ownership/accessors, or the complete translate_TLB_hit
WP. The generated hit still performs permission checking and possible A/D
update before its conditional refresh, with original-entry PPN/PBMT on success.
No such successful branch is supplied as a premise here. Cross-backend
correspondence remains the repository's separate obligation; source mapping
is not a Lean/Rocq equivalence theorem.

Frozen module SHA256:

- Defs: `c61b025deebe976676088f9ea3a52688aabdc9ece17780623eb29cdce63c1642`
- Spec: `6dfcca442bddc3976ad6e1660b5537b44fe336b09744089389be918eed42e77a`
- WordProofs: `17b0edf8af92853c6c52fba4d8d31ce41ec8601baadf2d7efd87fe1a2a89046f`
- Proofs: `3e14ac5e0b94c257d02d9c4c7057813bad73fb3b93685e03c98d55d7730a3efb`
- PlanProofs: `b31b7c308a9d63b74f81923bb2ffcb79d44b2f6ae43f208e0784ee7a84a1f56c`
- Link: `63f23b46a899b968bdfd44722914f3ae8bc9aaeceef262740b31971e1855f2fd`

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
