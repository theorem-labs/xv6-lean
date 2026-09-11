# Native cache, dirty flags and exception seal

`FsBlockGhost{Key,Defs,Spec,Proofs,Link}` are frozen after owner validation.
The approved design is `docs/design/fs-block-ghost-boundary.md`. The four
resource modules are accompanied by a small scoped key-order module.

| Exact pinned source | Lean mapping |
| --- | --- |
| `Xv6Cameras.v:361–385` | Three distinct fsLogG GhostMap cameras, slots 39 cache, 40 dirty, 41 exceptions |
| `FsBlocks.v:69–91` | Existing six-field `FsBlocks.Names`, reused verbatim |
| `FsBlocks.v:96–111` | `chalf`, `mclean`, `mdirty`, native Timeless instances |
| `FsBlocks.v:124–173` | Exact clean/dirty agreement, full-authority plus two-half cache update and dirty flip |
| `FsBlocks.v:776–794` | Exact singleton `exc_auth`, full `exc_own`, discarded-empty `exc_sealed`, Timeless/Persistent |
| `FsBlocks.v:796–832` | Exception allocate, agree, sealed-empty, same-name update and empty-handle persistence |

Cache keys and dirty keys remain signed Int. Cache values are arbitrary
byte lists at this layer; no 1024-byte premise narrows the source resource.
The cache client half and machinery half both use `DFrac.own (1:Qp).half`.
The clean machinery pairs its cache half with a dirty half at false; the
dirty machinery uses true. Agreement returns machinery bytes equal to
client bytes in the source order.

The update operations consume actual full authority and both held halves.
A checked private native half-update theorem proves agreement, joins the
halves, obtains authoritative lookup, updates the native map and splits the
new full element into two halves again. Both public operations return the
old agreement/lookup and all updated authority/halves. No half is silently
dropped and no update from a single half or authority alone is exposed.

The exception map has the exact source Unit key and finite extensional
sets of signed blocks as values. Lean's missing Unit ordering is supplied
by the tiny scoped `FsBlockGhost.Key` instances: constant-equal comparison,
checked transitivity and equality reflection. It introduces no global
Unit instance, numeric surrogate or additional possible key. The singleton
authority, full handle and discarded empty fragment are actual native
GhostMap resources, not separate pure claims or a replacement GhostVar.

Exception allocation returns singleton authority and its full fragment
while retaining the caller's frame. Lookup proves both full-handle agreement
and empty authority value in the presence of a seal. Full-handle update
allows arbitrary old/new sets, exactly as source; a shrinking-only rule is
not substituted. Sealing consumes only the empty full handle and persists
its actual element. No authority or independent recovery-completion premise
is required by this source operation.

The registry extends `IcacheTopRegistry.registry` at exactly 39–41 and
proves preservation of 0–38 and 42 upward. All prior capacities, native
invariant construction and top-registry Spec remain available in the same
world. `diskCapacity` is the existing signed byte camera at slot 12;
`disk_machine_same` proves it equals the actual machine-era disk capacity.
There is no second logged-byte camera. The six names, including cache,
dirty, bytes, link, top and exception names, remain caller supplied.

Validation: `python3 tools/lake.py build MachCSL.Logic.FsBlockGhostLink`
passes all 488 jobs. There are 53 public named theorems, one checked private
half-update theorem, eleven Timeless instances and one Persistent seal
instance, plus the three scoped Unit-order instances. Fresh
`/tmp/xv6-lean-research/FsBlockGhostOwnerAudit.lean` audits all 225 physical
module declarations, private/generated helpers, opaque bodies, types and
datatype constructors. Only `propext`, `Classical.choice`, and `Quot.sound`
occur; zero roots are excluded and no unsafe/partial or
`FsDurSnapshot.Initial` dependency occurs.

Explicit next dependencies are the actual BioView carrier and its disk/bio
resources, complete nine-leg byte invariant and crossing/recovery proofs,
row/seal packaging, source fs_alloc and region invariant construction.
None is represented by an opaque assumed predicate here. No existing
frozen source, repository umbrella or shared registry definition was edited.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
