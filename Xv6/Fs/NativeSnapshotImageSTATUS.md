# Native durable snapshot at the actual initial image

The literal leaf applies the reviewed source initial constructor to
`Image.snapshot_ok`: the exact pinned artifact's `imageState` with
13 inode blocks and its committed `homeMap`. It does not re-evaluate or
replace the existing image certificates.

The independent pure `home_lookup` theorem gives the exact committed
coverage: blocks 1 through 1999, excluding the 31 log blocks 2 through
32. `flattened_home_byte` proves that every byte found in the flattened
committed map equals `Image.disk` at the same signed address. It uses the
checked block width and original map restriction, rather than inferring
byte agreement from a ghost-allocation frame.

Three designated literal initialization callers instantiate the generic
native constructor: `allocate_snapshot` returns all three ghost names,
the six-leg snapshot and exact uncarved remainder; `allocate_durable`
returns the existential durable predicate; and
`allocate_with_physical_authority` preserves the supplied original disk
authority at **that same `Image.disk` value** beside the durable result.
Every rule preserves an arbitrary caller frame. The snapshot has its own
fresh byte name at the existing Disk camera. These are initial allocation
applications, not reboot/commit transport or full crash-invariant setup.

`NativeSnapshotImageAudit.lean` defines the reusable command
`audit_fs_initial_allocation`. It scans the current entire imported
Lean environment, including theorem and opaque bodies, and checks physical
module origins for six approved generic allocation/wrapper declarations
and three designated literal initial callers. The nine expected call
edges are checked. A new caller of any watched generic wrapper **or literal
leaf** fails the audit, so an unclassified intermediate runtime wrapper
cannot hide behind the image theorem. The command must also run after
all project umbrellas in CI to cover later imports. This use-site policy
is separate from logical linear ownership; the `Initial` namespace itself
does not prevent repeated applications.

Validation: building `Xv6.Fs.NativeSnapshotImageAudit` passes **583 jobs**.
The concrete leaf has **five theorems**. A fresh physical-origin audit
checks all **eight declarations** and their complete transitive types,
definition/theorem/opaque bodies, and referenced constructor fields:
standard `propext`, `Classical.choice`, and `Quot.sound` only, no unsafe or
partial semantic dependency, zero exclusions. The reusable call-graph
check also passes with both current `MachCSL` and `Xv6` umbrellas imported.
A negative fixture defining an unclassified wrapper around
`allocate_durable` fails with the intended caller-policy diagnostic.

Audit evidence in the working environment:
`/tmp/xv6-lean-research/NativeSnapshotImageOwnerAudit.lean`,
`NativeSnapshotGlobalAudit.lean`, and `NativeSnapshotNegativeAudit.lean`.
During audit development, an initial zero-edge result exposed the default
`ConstantInfo.value?` setting that omits theorem/opaque bodies. That result
was rejected. The final command explicitly sets `allowOpaque := true`;
the recent durable-byte, footprint, assembly, and snapshot owner audits
were rerun successfully with the same correction. The root global audit
already used this setting.

The generic snapshot and assembly checkpoints passed parent review.
The coordinator reviewed and approved this concrete leaf and audit; see
`docs/reviews/native-snapshot-image-review.md`. The root audit invokes the
caller check again after all project imports. Resource readback
and source-instance transport remain separate source dependencies; no
runtime path invokes a pure-input initial mint through this leaf.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
