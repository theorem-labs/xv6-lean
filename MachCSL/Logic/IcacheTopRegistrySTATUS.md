# Native top-map transaction registry and invariant

The five `IcacheTopRegistry{Defs,Spec,PureProofs,Proofs,Link}` modules are
frozen after owner validation. The approved design is
`docs/design/icache-top-registry-boundary.md`.

| Exact pinned source | Lean mapping |
| --- | --- |
| `Xv6Cameras.v:809,859`; `IcacheRef.icfg_lk` | Native GhostMap Nat ((Nat × Qp) × finiteSet Int), explicit arm-map name, new slot 38 |
| `InodeRegion.v:3015–3057` | `parked`, full `armed`, `clean`, complete `body` and actual native `invariant`; Timeless/Persistent instances |
| `3062–3080` | `clean_empty`, `allocate`: actual invariant allocation from supplied local top authority and same-name empty arm authority |
| `3086–3114` | `arm`: fresh arm id, exact transaction share parked, singleton inode-set receipt |
| `3124–3158` | `disarm`: restore one inode's local predicate using its actual top fragment and remove only that inode from the held receipt |
| `3164–3188` | `release`: consume an empty full receipt, delete its map entry and recover its exact transaction/share token |
| `3197–3230` | `parked_empty_of_no_ops`, `clean_access`: empty transaction authority refutes every parked positive share; return top authority, full local facts and mask-restoring continuation |
| `IcacheRef.v:1163` | Separate `allocate_empty` native camera rule with caller frame, for the later configuration allocator |

The full arm-map value preserves transaction Nat, positive Qp and finite
signed inode set, with the source tuple association. The authority is a
separate actual native GhostMap; it does not reuse filesystem links or
replace the top map. `armed` is its full-share fragment. The top authority
is the existing FsTop25 camera over complete arbitrary durable nodes. The
parked resource is the existing LogTx33 pin at exactly the entry's positive
share, including shares smaller than one. No pure pin or whole-transaction
premise replaces it.

The exact clean condition imposes the durable local inode predicate only
at an authoritative node absent from every suspended set. It imposes no
restriction on an armed node, and no arm set must already be a subset of
the inode-map domain. Pure insertion/disarm/deletion laws preserve this
contract. Disarming first obtains authoritative lookup agreement using
both the full receipt and the caller's top fragment; it does not infer the
node value from a free-standing equality. The native update retains the
transaction/share column, changes only the set, and returns the original
top fragment. Releasing returns the exact original share.

The invariant allocation consumes the supplied top and empty arm
authorities at their existing names. It allocates a native Iris invariant,
not replacement ghost-map authorities. Its local-node condition is the
source boot condition. The independent empty-camera constructor remains a
separate same-world configuration primitive; none of the invariant/runtime
operations calls it. The runtime arm derives freshness from the actual
finite arm map and inserts at that id; no caller freshness witness is used.

The clean accessor opens under E and returns under E minus the invariant
namespace. The top authority and unchanged empty transaction authority
remain outside while the returned continuation retains the arm authority
and the native invariant closer. Closing requires returning the same top
map authority and restores E. The result does not claim that the invariant
is already closed or that the caller can change the map without the source
local facts. The source namespace is represented by explicit N, preserving
all namespace-inclusion and mask-difference conditions.

The Link extends `IcacheEscrowTokens.registry` only at slot 38. Checked
preservation laws cover slots 0–37 and 39 upward; explicit old capacities,
slot equalities, machine aliases and existing invariant slots 16–19 are
retained. `nativeSpec` uses the same registry's actual InvGS. No new world,
initial snapshot allocation or replacement resource carrier occurs.

Validation: `python3 tools/lake.py build MachCSL.Logic.IcacheTopRegistryLink`
passes all 482 jobs. There are 51 named theorems (including registry/old
capacity links), five Timeless instances and one Persistent instance.
Fresh `/tmp/xv6-lean-research/IcacheTopRegistryOwnerAudit.lean` audits all
204 declarations from all five physical origins, including private/generated
helpers, opaque bodies, types and datatype constructors. Only `propext`,
`Classical.choice`, and `Quot.sound` occur; zero roots are excluded and no
unsafe/partial or `FsDurSnapshot.Initial` dependency occurs.

This closes the source top invariant's allocation and arm/disarm/release/
clean-access protocol. The source byte-view invariant, cache/exception
resources, `fs_bytes_row` and seal, region invariant packaging, further
top retagging operations and complete filesystem configuration allocation
remain separate source dependencies. None is assumed by this module.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
