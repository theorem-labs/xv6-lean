# Native inode-region invariant boundary

This boundary ports `InodeRegion.v:3239–3278` and the invariant-allocation
step of `IcacheBoot.v:871–886` at the pinned `arxiv-v1` source. It connects
the already implemented full inode-region body to the actual native Iris
invariant, actual logged-byte invariant, and actual top-registry invariant.

The owned implementation starts with `IcacheRegionInvariantDefs.lean` and
`IcacheRegionInvariantSpec.lean`. Native proofs and the registry Link follow
a review of these contracts. No existing frozen definition changes and no
new camera or ghost name allocation are needed.

The capacity stores the complete `IcacheRegionSlot.Capacity`, the existing
`FsBlockGhost.Capacity`, one `Disk.Capacity`, and the native top-arm-map
capacity. The byte invariant and logged byte view derive from that same
Disk capacity. The top invariant derives its FsTop and LogTx capacities
from the complete region capacity. Thus the columns cannot accidentally
use different instances through separately supplied duplicated capacities.
The eventual Link will select the existing registry through slot 41.

The names retain every `IcacheRegionSlot.Names` client field, all six actual
`FsBlocks.Names` fields, and the top-arm-map name. The logged view is exactly
`FsBytesGamma.logged disk filesystem`: its bytes, link and top names are
those of the same filesystem record. The top invariant takes that same
top name and the region's same transaction name. No independently named
byte-view predicate or assumed abstract invariant is substituted.

| Definition | Exact resource |
| --- | --- |
| `body` | Existing `IcacheRegionBoot.body` with the derived logged view; full record-map authority, all actual block/slot rows and covered registry |
| `topInvariant` | Actual `IcacheTopRegistry.invariant` at source `ftopN`, including its top authority, arm authority, parked transaction shares and clean condition |
| `ireg_reg` | Actual invariant at source `iregN`, unsealed `FsBytesInvariant.row`, and actual top invariant |
| `ireg_inv` | The same region invariant and top invariant, with `FsBytesInvariant.any` including the real discarded empty-exception seal |

The source namespace constants remain root children `ireg` and `ftop`.
The byte invariant keeps its existing separate source namespace. The
allocation rule accepts any Iris mask as native `inv_alloc` does; no
invented namespace-in-mask condition is required to allocate an invariant.

The public Spec has the four exact source projection/sealing laws:
`ireg_inv_reg`, `ireg_inv_of`, `ireg_inv_bytes`, and `ireg_inv_ftop`.
Both region bundles will receive native Persistent instances. A fifth
native allocation law consumes the actual supplied region body and retains
an arbitrary frame while packaging the supplied actual byte row and top
invariant. It does not allocate, duplicate or synthesize any slot client,
record authority, filesystem byte authority or top authority. It is the
final allocation step of source `ireg_alloc`, not a claim that its entire
preceding resource preparation has been discharged by this wrapper.

The arbitrary source `start` parameter remains independent of
`names.region.epoch.inodeStart`. The generic source `ireg_body` and final
invariant definition do not add an equality between these inputs. The
existing literal `IcacheRegionImage.imageNames` updates only that start
field to the actual superblock inode start (33), so later literal/config
composition can and must use the checked tie. This boundary neither
silently assumes it nor strengthens all generic callers with a new premise.

Validation will build only these owned modules, then audit every logical
declaration at their physical origins and every transitive type, opaque
body and datatype constructor. Only the standard three axioms are allowed;
no initial durable allocator, custom axiom, unsafe or partial logical cone
is permitted. Complete boot client allocation, recovery sealing and
configuration invariants remain subsequent source dependencies.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
