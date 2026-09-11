# Shared kernel page-table invariant composition

All six modules PureDefs/PureProofs/Defs/Spec/Proofs/Link compile. The final
nativeSpec discharges ownership, ghost and invariant dependencies using
native implementations at the same machine/view capacities. registrySpec
reuses the existing 48-slot family. No shared-translation or actual boot
publication theorem is claimed by this invariant layer.

TreeSpec matches KptTree.kpt_tree_spec_gen, including absent VPNs. The pure
proofs derive mapping lookup, absent blocking, canonical snapshot paths and
preservation after an A/D-only update at a mapped path. In particular they
do not claim canonicalization preserves every invalid nonleaf at level zero.

The invariant body is the exact source KptShare.v86–101: a full depth-two
pinned tree, canonical snapshot, one-shot bound plus actual log receipt,
full mapping authority and the complete TreeSpec. It has no current CPU,
TLB register, running context or second physical slot. Capacity.ghost derives
its Views from the same actual machine capacity.

Allocation consumes the existing physical tree, authority, log receipt and
both pending tokens. It shoots the actual one-shot cameras and allocates the
native invariant. This installs an already-pinned table; it neither allocates
physical pages nor establishes the source's context-to-pin boot transition.
Snapshot and path rules open with the supplied namespace mask, remove the
later using proved timelessness, and restore the complete body before returning.

Path lookup combines the actual map authority with the supplied persistent
mapping claim, then combines actual snapshot agreement with the pure tree
transport proof. It temporarily extracts the three physical slots to derive
RAM at both endpoints and exact alignment. The restoration wand consumes
all three slots, and the same tree/map/body closes the invariant. Returned
leaf A/D bits are existential; no current read word, legal view receipt or
successful memory event is manufactured.

The final shared event rules must still open and close at each real ordinary
read, exclusive reread and conditional write. TLB coherence, whole translated
instructions and actual boot setup remain separate.

Validation: the closed native target passed706 jobs. The full audit checked
all39 declarations in six modules, including types, opaque bodies and
constructors: standard three axioms only, zero exclusions and no unsafe or
partial semantic dependencies. Independent interface/pure review passed its
26-declaration four-file snapshot; full implementation review is in progress.
Evidence: /tmp/xv6-lean-research/KptSharedAudit.lean and kpt-shared-audit.log.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
