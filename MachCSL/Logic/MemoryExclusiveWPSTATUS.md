# Native exclusive RAM reads and reservation custody

Source: pinned `HartEvents.v:49–78,383–482,763–790` and the read-node
specializations `HartSMem.v:4693–4762`, at xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The generic rule `wp_exclusive` retains the actual dependent `ReadRequest n`
and its continuation. Its only request guards are exactly
`deviceAddress req.pa = false` and `accessExclusive req.access_kind = true`.
The original address, access kind and strength, virtual-address field,
translation, tag and width remain in the emitted event; the result is the
actual `.Ok (word, none)`. No alignment, maximum-access-size, nonzero-width,
or no-wrap premise is added to the event leaf. These checks, when applicable,
belong to the generated instruction code that produces a request.

`blocked_step`, `acquired_step`, and `step_inv` characterize both actual live
machine arms. A blocked read retains its exact cursor, clears its own
reservation, and leaves its view and all other machine fields unchanged.
A successful read uses `readBytes` of current physical RAM, sets the view to
the current log length, and installs `some (snapshot pa n word)`. It changes
neither memory nor log. The field and writeback proofs retain registers,
devices, generation, power, era image and all other CPUs' views/reservations.
`read_current_top` proves that this flat read is the actual TSO read at the
log top under `MemoryOK`.

`exclusivePremise` follows the source callback staging. The rule first
advances the real TSO view and mints its top receipt. The callback receives
the native register/heap/device bundle, that advanced TSO interpretation,
and the receipt. It chooses a word by proving `readBytes` of the current
memory succeeds, and closes the same bundle and advanced TSO interpretation
under the guarded return-mask update. The rule frames disk and reservation
authorities and the remaining fixed interpretation. It pays the actual
snapshot update, proves `ReservationsOK` via `snapshot_submap`, restores
the complete era and fixed state, and hands the real snapshot fragment to
the continuation. The callback supplies no successor-preservation theorem.

The native bundle contains the complete global register interpretation,
where source `mstate_interp` exposes the focused register interpretation.
This granularity adaptation is explicit in `readBundle`; the callback must
return the same global bundle. The source's generalized `mctx`/`swp`
composition and generated `read_ram` request/resume wrapper are separate
work, not claimed by this direct-event implementation.

The private guarded retry proof uses `resvAny` to quantify over the exact
old snapshot. On a blocked step it calls the proved
`RestartWP.power_clear`, obtains the `none` fragment, and reuses the
unchanged callback. The public rule takes the source's exact `resvFrag rr`.
There is no disjointness precondition excluding contention, fairness
assumption, or bounded-retry premise. Older generations follow the actual
dead-thread step and native dead-thread WP. Both live arms preserve the
fixed observation interpretation through their actual silent machine step.

`wp_bytes` is a concrete specialization: ordinary fractional physical byte
ownership proves the current flat read via full native `Heap.valid`. It
returns the same bytes, the real snapshot fragment and the top view receipt.
It requires no timestamp ownership or pristine-memory assumption and
assumes no read result. The callback form permits an invariant to choose
the word at the step and close before the continuation, as needed by
source `swp_read_ram_node4_racq_ex`.

`held_submap` combines a live generation certificate, full state authority,
the actual reservation fragment and `ReservationsOK` to establish that a
held snapshot is still a submap of current RAM. `snapshot_read` and
`held_snapshot_read` recover the original word under the explicit source
bound `n < 2^64`; this excludes aliasing within the modular window without
requiring alignment or a non-wrapping base interval. The proof reuses
`TsoStore.windowMap_decode` and its checked offset injectivity. A reservation
fragment alone is neither byte ownership nor an unconditional read fact.
These two custody laws are exposed as `heldSubmap` and `heldSnapshot` in the
independent `MemoryExclusiveWPSpec` for conditional-write clients.

`MemoryExclusiveWPLink` instantiates the implementation at the existing
shared 23-slot registry with supplied native invariant names. No new camera
or invariant world is allocated, and generic-capacity proofs remain usable
at later registry extensions.

Validation: `python3 tools/lake.py build MachCSL.Logic.MemoryExclusiveWPLink`
passed 447 jobs; the final proof module compiled in 1.6 s and link in 743 ms.
`python3 tools/lake.py env lean /tmp/xv6-lean-research/MemoryExclusiveWPAudit.lean`
checked all 45 physically originating declarations, including private and
generated helpers, and their complete statement/proof dependency cones.
Only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms; no
unsafe or partial semantic dependencies occur. No runtime companions were
excluded.

Conditional writes, reservation-preserving register windows, generated AMO
instruction execution, lock invariants and mutual exclusion remain separate
proofs. This layer introduces no fused AMO transition or new closed machine
safety claim. Independent root review passed; see
`docs/reviews/memory-exclusive-wp-review.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
