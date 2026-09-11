# Complete native inode slot and pointwise boot

The five `IcacheRegionSlot{Defs,Spec,Proofs,BootProofs,Link}` modules are
frozen after owner validation. They assemble the complete native source
`InodeRegion.v:2634–2730` slot and its pointwise boot routing from
`IcacheBoot.v:773–842`. The approved design is
`docs/design/icache-region-slot-boundary.md`.

| Source | Lean mapping |
| --- | --- |
| `InodeRegion.v:806–808,1145–1151,1412–1430,1530–1553` | Exact marked/in/type/link validity predicates and pure projections/stability |
| `2634–2689` | Complete `ireg_slot`, with the source existential body and outer epoch/link resources |
| `2673–2683` | Exact native IN/MARKED versus PENDING `arm`, without identifying separate existential registry pairs by definition |
| `2691–2730` | Timeless slot and introduction from every source component |
| `IcacheBoot.v:630–641` | Conditional free-node `topBoot`; no resource required at a nonzero type |
| `IcacheBoot.v:773–842` | Native `boot_slot` from supplied pointwise components, with source record/marker routing |

The existential body retains r, the complete raw claim cell, the complete
raw freeze cell and count n. Its columns are reference authority plus the
count relation; exact link validity; absent-claim/native-open disjunction;
count half; pure claim and freeze validity; paired native claim/freeze
shelters; mirror half; and the complete arm. The outer epoch receipt and
filesystem link custody retain their source association. In particular,
link validity is zero type implies zero links, unsigned links at most 32767,
and type in 0/1/2/3. It does not add a pure root-allocation condition.

The nonpending arm holds either IN with record and guarded top park, or
MARKED with marker, together with a full native registry row. The pending
arm holds a zero-type record, the structural half row, actual
`region_pending` and the guarded top park. The second half and committed
lower bound are inside the real pending resource. The two existential
escrow-name pairs stay separate until native agreement relates them.
There is no escrow invariant hidden in the Timeless predicate. The native
`arm_record_out` proof uses held full-record exclusivity to exclude both
record-inside alternatives and returns the marked condition, marker, full
registry row and caller's original record fragment.

`bootInput` owns the supplied record and marker, unclaimed/unfrozen zero
reference authority, zero observation authority, full registry row, count
and mirror halves, filesystem link custody and conditional free-node top
fragment. `boot_slot` takes a 32-bit inode and only the exact link-validity
and free-record bare premises. It builds the existing observation receipt
from the supplied zero authority, builds the zero reference/mirror columns
and off/absent shelter, and routes the existing resources. At type zero,
the slot holds the record and the caller receives the marker; otherwise the
slot holds the marker and the caller receives the exact record. The whole
slot/out/frame bundle is under one basic update. The arbitrary caller frame
is preserved in both cases.

No ghost name, record authority, reference ledger, registry, filesystem link
or top resource is allocated by the pointwise theorem. It does not require
an already allocated invariant or a pure substitute for any resource. The
native Link packages existing capacities from `IcacheEscrowTokens.registry`
through slot 37; no new camera or registry extension is introduced. All
names remain explicit, including observation names and signed inode-start
geometry. Generic signed slot keys are unrestricted; the pointwise boot
input's 32-bit inode directly matches the source outside-fragment API.

Validation: `python3 tools/lake.py build MachCSL.Logic.IcacheRegionSlotLink`
passes all 497 jobs. There are 14 named theorems and four Timeless instances.
Fresh `/tmp/xv6-lean-research/IcacheRegionSlotOwnerAudit.lean` audits all 81
logical declarations from the five physical module origins, including
private/generated helpers, all opaque bodies, types and datatype constructor
types. Only `propext`, `Classical.choice`, and `Quot.sound` occur; zero roots
are excluded and there are no unsafe/partial or `FsDurSnapshot.Initial`
dependencies.

This closes the actual slot definition and pointwise boot composition.
Finite-region distribution, region block and registry coverage, region
invariant allocation, free-pool and escrow bodies, actual image-wide inode
boot and complete filesystem initialization remain subsequent source
obligations. They must use these proved native components and the existing
byte resources; none is assumed by this boundary.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
