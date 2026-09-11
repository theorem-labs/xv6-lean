# Context pin mint: frozen

All seven modules compile (434 jobs). The coordinator approved Defs/Spec before
implementation; all fourteen signatures remain unchanged. Native Link supplies
the complete Spec at arbitrary supplied capacities, the existing context
registry, and any complete era capacity.

The own-view route uses only ownPub≤view. The log-top route gives no view
receipt. The separate agent-zero boot route carries per-byte zero/own-message/
view anchors. Every mint preserves the same full heap and TSO interpretation;
all supplied running-context tokens are retained. No camera, allocator,
physical-state mutation or strengthened whole-log drain is introduced.

The actual timestamp authority and full held fragment change None→Some pin.
Latest plus the native heap identifies the owned byte. Boot own-message anchors
use that byte's Latest witness and the corresponding actual log receipt;
dirty-set membership alone is insufficient. The byte-run induction retains
each exact floor and slotAnchor, proving only floor≤log.length. It never
replaces those anchors by a log-top view receipt.

Fresh full physical-origin audit: 62 declarations in all seven modules,
including private/generated helpers, types, opaque bodies and datatype
constructors; only propext/Classical.choice/Quot.sound, zero exclusions, no
unsafe/partial or Initial dependency in logical cones. Six additional kernel
checks pass, including own-publication versus foreign-log-top examples and
exact one-byte/empty boot runs.

Mapping: `docs/design/context-pin-mint-boundary.md`. Evidence:

- `/tmp/xv6-lean-research/context-pin-mint-build.log`
- `/tmp/xv6-lean-research/ContextPinMintOwnerAudit.lean`
- `/tmp/xv6-lean-research/context-pin-mint-owner-audit.log`
- `/tmp/xv6-lean-research/ContextPinMintChecks.lean`
- `/tmp/xv6-lean-research/context-pin-mint-checks.log`

Canonical PTE allowed-set specialization and UTier→KTier tree publication
remain the next source dependency. Full boot reachability and translation WP
are not claimed here. Existing frozen files and umbrellas are unchanged.

Independent coordinator review and fresh 62-declaration full audit pass.
See docs/reviews/context-pin-mint-peer-review.md.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
