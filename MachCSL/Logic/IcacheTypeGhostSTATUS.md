# Native inode generation type one-shot and boot regime

The four `IcacheTypeGhost{Defs,Spec,Proofs,Link}` modules implement the exact
source non-unital `ityR` camera and native ownership laws. The approved source
inventory is in `docs/design/icache-type-boundary.md`.

| Pinned source | Lean implementation |
| --- | --- |
| `Xv6Cameras.v:607–613` | `TypeRA = Csum (Excl Unit) (Agree (DiscreteO (BitVec 16)))`, constant functor and explicit capacity |
| `IcacheRef.v:1192–1233` | `ity_pending`, `ity_shot`, Timeless/Persistent distinctions, arbitrary-type shoot, shot agreement, pending/pending and pending/shot exclusion |
| `IcacheRef.v:1256–1298` | `ireg_boot`, existential `ireg_open`, exact Boolean-indexed `ireg_regime`, and native boot/open/regime exclusions |
| `FsReady.v:385–391` | `fs_ready_seal` consumes pending and uses the exact zero shot witness |
| `IcacheRef.v:1151,2178` | Isolated native `allocate_pending`, fresh name in the supplied GF with arbitrary frame retained |

The complete raw Csum and Excl carriers remain present, including both invalid
forms. The camera is not converted to a unital camera or replaced by a ghost
variable, type equality, or global authoritative map. All updates, validity,
agreement, exclusivity and persistence use the actual native Iris cameras.

A shot's type is any `BitVec 16`, including zero. Neither pending nor shot
implies a physical inode type or allocatedness. Both zero and nonzero firing
are exported as checked examples; the source's nonzero record conditions
belong to later payload and inode rules. The existential open token contains
actual shot ownership. Only the true/runtime regime is Persistent; false is
the exclusive boot token, while both branches are Timeless.

`shoot_frame` retains an arbitrary caller frame while consuming same-name
pending. `allocate_pending` allocates only a fresh pending name in the current
world; it does not recycle an existing name, replace authority, or construct
an InvGS world. Its sole direct logical caller in this prefix is `actual`,
which packages the generic specification. There is no literal boot or runtime
liveness caller in this prefix. The complete `live_genlo_bump` law still needs
the actual liveness map and its full-share premise.

`claim_guard` is the local consequence of the already supplied slot guard
`c = none ∨ ireg_open` and the actual boot token; it returns the boot token.
It does not open or establish the inode-region invariant and is not the
source `IregLinkNz.ireg_boot_no_claim` accessor. The complete freeze shelter
`ireg_fsh` also requires the indexed transaction/share token; it is not
weakened to a regime-only predicate here. Transaction pins, freeze shelter,
full payload/liveness rules, fsinit execution and the complete `fs_ready`
resource remain subsequent exact source dependencies.

The new registry extends `IcacheRefLedger.registry` only at assigned slot 32.
`registry_old` proves all slots 0–31 unchanged and `registry_unused` proves
all slots 33 onward unchanged. Explicit established capacities and their
native specification links are retained, including count/mirror/window pin
28–30, reference ledger 31, inode record 27, held set 26, filesystem top 25,
lock 24, filesystem links 23, and the prior machine/invariant resources.
A single camera slot supports separate ghost names for each generation and
for the boot regime.

Validation: `python3 tools/lake.py build MachCSL.Logic.IcacheTypeGhostLink`
passes 464 jobs. There are 44 named theorems and the native camera/predicate
instances. The physical-origin audit is
`/tmp/xv6-lean-research/IcacheTypeGhostOwnerAudit.lean`; it traverses all types,
opaque bodies and datatype constructor dependencies, rejecting nonstandard
axioms, unsafe/partial logical dependencies and `FsDurSnapshot.Initial`.
All 163 logical declarations pass with only `propext`, `Classical.choice`,
and `Quot.sound`; zero roots are excluded and no unsafe/partial or initial
allocation dependency occurs.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
