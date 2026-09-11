# Native top-map transaction registry

Approved source boundary: `InodeRegion.v:3015–3230`, with exact carrier
`Xv6Cameras.v:809,859` and explicit name `IcacheRef.icfg_lk`. Owned modules
are `IcacheTopRegistry{Defs,Spec,PureProofs,Proofs,Link}` and STATUS.

The new slot 38 is precisely the native GhostMap camera from natural arm
identifiers to `((Nat × Qp) × Std.ExtTreeSet Int)`. It preserves all old
slots 0–37 and all slots 39 upward. This is separate from filesystem links,
transaction authority and the top inode map. Names for the top map, arm
registry and transaction ledger are explicit and distinct fields; no
injectivity premise is imposed on their numeric values across cameras.

`parked` owns the recorded positive share of the recorded transaction's
actual LogTx pin. `armed` is the full arm-map fragment naming its complete
transaction/share/set value. `clean I A` requires the actual durable local
inode predicate at each I entry that no A entry suspends. `body` owns both
full native map authorities, all parked shares and exactly this pure fact.
The invariant uses native Iris `inv`, with an explicit namespace so later
source namespace composition can select the source `ftop` namespace.

The public laws allocate the invariant from a supplied local top authority
and supplied empty arm authority at the same names; insert a fresh arm id
while parking any positive transaction share; disarm one inode after proving
its actual local condition and supplying its top fragment; and release an
empty receipt to recover its exact parked transaction share. The clean
accessor opens the actual invariant under E with its namespace removed,
uses supplied empty transaction authority to prove the arm map empty, and
returns top authority, all local facts, unchanged empty transaction authority
and the mask-restoring continuation. It does not close the invariant before
returning the top authority. Native freshness is derived from the finite
arm map; no caller freshness oracle is introduced.

Generic camera rules are proved at explicit capacities; invariant laws
also require the existing same-world InvGS. The Link reuses FsTop25,
LogTx33 and invariant slots16–19 and exports all earlier capacities.
Allocation of an empty arm map may be supplied as a separate native algebra
lemma for the eventual configuration allocator; the invariant constructor
itself does not replace the caller's authority. No full icache configuration,
byte invariant, recovery seal, `fs_bytes_row`, region invariant or whole
filesystem boot is claimed. In particular the source byte invariant's
cache/exception resources remain a separate dependency.

Definitions and source contracts precede proofs. Validation covers all
physical module declarations, opaque bodies, type and constructor dependencies;
only the standard three foundational axioms are allowed. No initial snapshot
allocator or pure validity substitute is used by these runtime operations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
