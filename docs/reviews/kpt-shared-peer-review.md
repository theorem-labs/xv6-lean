# Shared KPT invariant: independent native review

PASS for the six frozen modules `KptSharedPureDefs`, `PureProofs`, `Defs`,
`Spec`, `Proofs`, and `Link`. This review was performed by the Codex artifact
agent independently of the coordinator who authored those modules. I authored
the separately reviewed KptOwnership dependency; this report does not claim
an independent re-review of my own ownership implementation.

I read all six modules and matched the body, publication and snapshot rules
to pinned `iris/KptShare.v:73–148`, and the complete mapping predicate and
A/D preservation proof to `iris/KptTree.v:331–389`. The source pin is
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The body retains all five source conjuncts: the full pinned physical tree,
canonical snapshot, existential publication bound with real log receipt,
full mapping authority, and complete map/absent-map TreeSpec. Namespace
parameterization generalizes the source fixed `kptN`; `kernelShared` names
that source specialization. The source one-bit A/D parameters are represented
by the existing checked Bool leaf constructors. Arbitrary upper raw words,
including G and RSW, survive the canonical path transport.

Allocation consumes the already-owned physical tree and both pending ghost
tokens, performs native shots, and calls native `inv_alloc`. It neither
mints physical ownership nor establishes initial publication resources.
Snapshot and path access open only with the explicit namespace inclusion,
remove the later using proved body timelessness, and return the entire body
through the native closure before the fancy update ends. Path access checks
both actual mapping authority and canonical snapshot agreement. It derives
address geometry from three physically owned slots and restores those same
slots. The returned leaf is an existential A/D variant of the supplied
snapshot, not a claim about a current hardware read.

The pure update proof preserves both present and absent mapping cases. Its
source auxiliary map/variant hypotheses are derived from the complete
TreeSpec rather than replaced by new assumptions. The proof does not assert
that arbitrary invalid nonleaf words are preserved by canonicalization.
`nativeSpec` and `registrySpec` discharge the generic ownership premise using
the actual native implementation, with the same machine/view capacities.

Independent validation: `python3 tools/lake.py build Xv6.Kernel.KptSharedLink`
passed all 706 jobs. `/tmp/xv6-lean-research/KptSharedPeerAudit.lean` independently
checked every one of the 39 physical declarations across all six modules,
including private declarations and complete type, opaque-body and constructor
cones. Only `propext`, `Classical.choice`, and `Quot.sound` occur; there are
zero exclusions and no unsafe or partial dependencies. Raw result:
`/tmp/xv6-lean-research/kpt-shared-peer-audit.log`.

No implementation correction was required. The status file still described
the closed Link as pending at review time; I notified its owner. Actual
shared read/exclusive/write events, boot publication, TLB coherence and
translated execution are separate follow-up proofs.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
