# Native filesystem type-register and link-count camera

Source: `Xv6Cameras.v:ity,fsLinkElemUR,fsLinkUR` and `FsStateLink.v`
sections1–5b at xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The carrier is exact: `IType.file | IType.directory (parent : Int)`, finite
multisets `Iris.Std.ListPerm IType` (lists quotiented by permutation), native
`LeibnizMultiSet`, native `Auth`, and an outer finite `ExtTreeMap Int`.
ListPerm's proved multiplicities and finite enumeration implement stdpp's
finite multiset laws. No count/agreement product or abstract validity premise
replaces the source camera. Two explicit instance applications select the
existing generic Heap camera; they introduce no new algebra laws.

Uniform replicas have zero/successor/addition, size and membership laws.
Native ownership gives both the fragment-count bound and exact type/parent
agreement. The authority can change its type at multiplicity zero by equality.
An empty fragment remains a present outer-map key and is not the map unit;
its split from authority is proved explicitly. The zero return branch does
not impose a type equality, matching the source.

Native frame-preserving updates prove one-at-a-time and batched mint/return,
including an arbitrary retained frame. Pile splitting, bounded prefix splitting
and list routing are proved. Whole-family allocation requires actual camera
validity. The full authority-plus-all-fragments element is independently proved
valid and allocatable. `FsLinkSpec` is implemented by these concrete native
proofs. Pure regression theorems reject a wrong directory-parent fragment and
any fragment at zero authority multiplicity.

The registry reserves slot23 and preserves all prior0–22 slots. It exports
explicit UART, native invariant/InvGS, heap, era and machine capacities at the
same runtime slots and maintains the shared-byte/shared-counter identities.
Runtime GNames remain explicit arguments; the capacity alone owns no resource.

Validation: `python3 tools/lake.py build MachCSL.Logic.FsLinkLink` passes
380 jobs (proof module 1.0s, audit/link module 1.1s). The link module audits all 186 public/private FsLink declarations
transitively, permitting only `propext`, `Classical.choice` and `Quot.sound`.
No native certificate or custom axiom is accepted.

Remaining source layers: section6's generic map gathering and the source
per-node/global `link_elem` construction, existential directory marker/type
assignments, root keep-alive slack and the actual initial-image link-validity
proof. This camera foundation does not assume or claim any of those results,
`FsDurSnap.snap_ok`, filesystem resource allocation, or whole-system adequacy.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
