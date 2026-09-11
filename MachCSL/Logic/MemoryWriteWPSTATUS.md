# Native RAM write event rules

`MemoryWriteWP{Defs,Spec,State,Proofs,Link}` implements the present-payload
RAM write rules corresponding to `HartEvents.v:797` (`swp_hart_ram_write`)
and `:841` (`swp_hart_ram_write_cond`) at artifact pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. These are actual native
`NotStuck` WPs for the existing `Machine.Step` language and fixed
`MachineInterp.irisGS`, with separate public contracts and linked proofs.

`WriteRequest n` is the complete dependent Sail request. The rule retains its
access kind, virtual and physical addresses, translation, signed declared
size, optional payload and optional tag. Its operational premises are exactly
a present payload and the RAM classifier. No alignment, width bound or access
kind restriction is added to the generic write rule. Successful execution
returns the actual `Ok none` and calls the actual continuation.

`writeState` expresses the real memory update, one hart-authored snapshot
append, reservation clearing, and classifier-dependent view: exclusive access
advances to `oldLog.length + 1`, while ordinary access retains the old view.
`written_step`, `blocked_step` and `step_inv` prove actual existence and
exhaustive successor inversion. A conflicting write preserves the request,
continuation, complete state and exact reservation fragment. A guarded Löb
proof retries that arm without invoking or spending the write callback.
Dead-generation execution uses the existing dead-thread transition. A forged
absent-payload event has no live successor, as `absent_event_no_step` proves;
the real builtin's absent-payload branch returns purely instead.

The generic `checkedPremise` is the source-style single-event resource
callback. It receives the complete global-register/full-heap/device bundle
and full TSO interpretation. Under the actual top-to-empty mask transition
and later, it must return those resources at precisely `writeState`, plus
the continuation awaiting the cleared reservation and exact post-view receipt.
The rule pays reservation-authority updates and all remaining era/fixed
framing itself. Reservation preservation is proved from the actual union of
other harts' reservations and `ReservationsOK`; no pairwise-disjointness
assumption is introduced. The fixed durable disk, generation counters,
registry and complete observed trace retain their actual ties.

`wp_write` supplies the trivial pure callback fact. `wp_conditional` instead
requires the exact snapshot reservation and `n < 2^64`, then derives
`readBytes currentMemory pa n = some old` from the native reservation/state
interpretation. It passes this fact to the callback. It does not assume the
old physical bytes and does not require `accessExclusive = true`, since the
source conditional rule imposes no such extra premise. The actual request
classifier still determines the post-view.

`ledgerPremise` is a resource-extraction interface, not a callee-WP oracle.
It returns the original bundle/TSO, an actual full source `ledgerWindow`, and
a closing continuation. `bundle_store` and `ledger_premise` consume that
window using the proved `TsoStore.StoreSpec.window` update, preserving full
heap metadata and every untouched timestamp payload. They return the new
`storedWindow` at `oldLength + 1` and the exact authored message receipt to
the caller's closing continuation. `wp_ledger` applies this adapter under
`n ≤ 2^64`; `wp_conditional_ledger` combines it with the stricter source
snapshot-read bound. Neither bound becomes a premise of generic RAM writes.

`Contracts` separates the store, view, reservation and exclusive-read validity
interfaces from their implementations. `nativeContracts` discharges every
field. `registryMemoryWriteWPSpec` instantiates all four public rules at
`FsLink.machineCapacity` and the same supplied native invariant world.
No camera, ghost name, alternate machine language, or second byte authority
is introduced. The `State` helper module contains the concrete successor,
reservation and complete-resource framing proofs.

Validation: `python3 tools/lake.py build MachCSL.Logic.MemoryWriteWPLink`
passes 454 jobs (state proof 1.0 seconds, main proof 1.2 seconds, link under
one second). A fresh physical-origin audit covers all 58 declarations in
all five modules, including private helpers, and traverses their complete
type/body/constructor-field dependency cones. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. No unsafe or partial logical
dependency is present, with zero excluded runtime companions. Records:
`/tmp/xv6-lean-research/MemoryWriteWPAudit.lean` and
`memory-write-wp-audit.log`. No `sorry`, custom axiom, `native_decide`, or
`bv_decide` is used.

This checkpoint does not prove MMIO writes, a complete generated AMO
instruction, a barrier rule, a lock invariant, spinlock mutual exclusion,
or a new closed machine gate. Those layers must instantiate the resource
callbacks using their actual resources and compose all interruptible events.
The conditional rule's native reservation bridge is linked from the frozen
`MemoryExclusiveWPSpec`; no exclusive-read implementation is imported by this
proof module. Cross-prover source correspondence remains a separate obligation.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
