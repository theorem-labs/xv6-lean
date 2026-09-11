# Physical KPT publication and shared allocation

This is the implemented native publication boundary `Xv6.Kernel.KptPublish`.
The entire pinned `KptPublish.v` (551 lines) has been read, together with
`KptShare.v`'s body/allocation/credential definitions and the existing native
KptOwnership, KptShared and ContextPinMint interfaces. The source pin is
xv6iris arxiv-v1 `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
The coordinator approved all fourteen Defs/Spec contracts before implementation;
all now have kernel-checked proofs and a concrete native Link.

## Exact contracts

There are fourteen obligations: one pure membership fact, eleven physical
publication contracts, and two composed invariant-allocation contracts.

| Lean contract | Source | Content |
|---|---|---|
| `PureSpec.slot_set_self` | KptPublish63–72 | Every raw 64-bit word's byte is in its canonical slot family, for arbitrary Nat offset. No valid-PTE/content premise. |
| `Spec.pin_word` | KptPublish93–104 | Common-bound pinned word plus agent-zero view receipt becomes the existing anchored kernel slot; each floor is that common bound. |
| `slot_view`, `slots_view` | KptPublish106–134, with its word step exposed | Own-publication drain plus explicit agent-zero view receipt; full user slots become kernel slots at this CPU's view. |
| `page_view`, `tree_view` | KptPublish140–257 | Fold over the existing 512 indices and depth-recursive existing tree ownership, preserving node claims and exact inert tree. |
| `publish_view` | KptPublish272–296 | Agent-zero publisher derives the needed view receipt from the actual TSO authority; returns both current-hart view and log-bound receipts. |
| `slot_boot`, `slots_boot` | KptPublish445–489 | Agent-zero boot publication with individual byte floors/anchors at a common log-length upper bound. No drain. |
| `page_boot`, `tree_boot` | KptPublish491–532 | The same owned tree is transformed recursively; no view receipt introduced. |
| `publish_boot` | KptPublish534–549 | Boot tree transformation plus actual log-length receipt. |
| `AllocationSpec.allocate_view` | Above own-view gate + KptShare112–130/159 onward | Transform the depth-two user tree, consume existing map authority and two unset tokens, and allocate actual shared invariant; return snapshot, bound and source per-hart credentials. |
| `AllocationSpec.allocate_boot` | Above boot gate + same KptShare allocation/credentials | Same composition at log length; credentials use the separate agent-zero boot arm, with no current-log-top view fact. |

The source's generic slot list uses signed Int keys. `slotsOwn` generalizes
the index carrier to Type without assuming equality/order or unique keys;
Int and the existing nine-bit page indices are both direct instances. The
list order, duplicate entries and empty-list behavior are retained. The
children folds of source165–225 are proof support for depth recursion, not
assumed successful tree transformations. At depth zero the existing inert
child descriptions still contribute no child ownership.

## Conditions that must stay separate

`ContextPinMint.Drained cpu g` is exactly
`ownPub (hartAgent cpu) g.log ≤ g.views cpu`. It does not require log length
to be at or below the CPU view. The generic drained slot/page/tree contracts
also require `viewZero (g.views cpu)`, exactly as the source does. Another
hart's receipt cannot supply the hard-coded zero-agent slot anchor. The
self-contained `publish_view` therefore requires `hartAgent cpu = 0` and
derives the zero-agent receipt from the current hart's actual view receipt.

The boot route requires that same agent identity but no drain. The already
proved ContextPinMint boot gate preserves each exact byte's zero/own-message/
view anchor and floor; the global tree bound is merely log length. A generic
log-top pin without such an anchor is insufficient for existing kernelSlot,
so there is deliberately no unanchored top-only tree publication contract.

Both transformations require actual full user-tier ownership. They need no
TreeSpec or pure valid-tree assumption: node claims and all 512 physical slots
already reside in the input ownership. They preserve those node claims,
all raw words, exact children and depth. The allocation contracts separately
require exact `KptShared.TreeSpec` for the input tree and mapping, including
absent-map VPNs, together with actual map authority and the two existing
one-shot unset tokens. No pre-pinned replacement tree is input.

## Names, native resources and implementation route

Capacity is exactly `KptOwnership.Capacity`. `contextCapacity` projects the
same machine's heap, views and history; `contextNames` projects the same era's
byte/timestamp/log/view/metadata names. `heapAt` includes the full gen_heap
metadata. `tsoAt` is the existing actual-state TSO interpretation at the era
image. `running` is the existing owned context token. Every publication and
allocation returns all three at the same state and names.

`PteCanonical.setAD_refl` and the existing byte-family facts support arbitrary
word self-membership. `KptOwnership.aligned_iff` connects the source model's
alignment Boolean to the arithmetic alignment retained by ContextPinMint.
No changed word decoder, restricted family or hardware-validity axiom is needed.

The allocation contracts compose the proved transformation with actual
`KptShared.allocate`. They use the caller's existing InvGS world and mask,
shoot the supplied tree/bound unset tokens at their existing names, and place
the transformed tree and supplied map authority in the actual five-leg body.
The returned snapshot, bound and length/view receipts are persistent; their
reuse in the separately returned per-hart credentials is supported by the
native cameras. No camera, era, physical memory or context is allocated.
The existing namespace-parametric invariant allocation rule does not require
an invariant-opening mask-inclusion premise; these contracts follow it.

## Validation and remaining integration

The initial `KptPublishSpec` signature build passed (413 jobs). The completed
`python3 tools/lake.py build Xv6.Kernel.KptPublishLink` passes (721 jobs).
All fourteen approved contracts remain unchanged. The seven modules are Defs,
Spec, PureProofs, SlotProofs, TreeProofs, Proofs and Link.

`kids_transform` implements the source persistent per-child update-wand fold.
`tree_view` constructs that wand from depth induction and the persistent
agent-zero receipt; `tree_boot` constructs it from depth induction and the
pure agent-zero identity. No public tree theorem assumes an unproved child
transformation. Both native allocation proofs first invoke the actual owned
user-tree transformation and then the actual KptShared native allocator on
that exact resulting tree and the supplied map/unset resources.

The complete physical-origin audit checks all 76 declarations, including
private/generated helpers, types, opaque bodies and datatype constructors.
Only propext/Classical.choice/Quot.sound occur, zero exclusions, no
unsafe/partial or Initial dependency in logical cones. Six additional kernel
checks cover invalid/raw PTE self-membership, a nonleaf singleton byte,
unrestricted out-of-word byte offsets, empty slot lists and arbitrary inert
children at depth zero.

Evidence under `/tmp/xv6-lean-research/`:

- `kpt-publish-signatures.log`, `kpt-publish-build.log`.
- `KptPublishOwnerAudit.lean`, `kpt-publish-owner-audit.log`.
- `KptPublishChecks.lean`, `kpt-publish-checks.log`.

Existing frozen modules, capacities and umbrellas remain unchanged. The
native transformation and shared allocation are now established; source boot
reachability, the fence execution site and full translated-function contracts
remain later integration obligations. No concrete page-table construction or
initial owned tree is inferred from its inert TreeSpec alone.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
