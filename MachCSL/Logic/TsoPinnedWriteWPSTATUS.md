# Pinned conditional RAM event boundary

Four modules are frozen: TsoPinnedWriteWP Defs/Spec/Proofs/Link.
All three public Spec contracts are inhabited by `actual` and `nativeSpec`.
The design is `docs/design/supervisor-pte-write-boundary.md`.

`pinWindow` and `storedWindow` are aliases of the existing pinned-store
resources with the actual machine capacities and era names. `bundle_store`
constructs the floor/set map using modular address subtraction and proves
its correspondence at every offset below eight. It then applies the native
registered-pin store gate to the actual `MemoryWriteWP.writeState`,
updating full heap metadata, byte/timestamp authorities, history, views and
TSO interpretation together. Global register/device authorities are framed.
No global no-wrap premise, changed payload family or camera is introduced.

`window_bytes` is a physical-fragment projection for pure validity queries.
`heap_word_read` derives actual full-state readback, and
`held_word_agreement` combines it with the native held-snapshot theorem to
prove that the physical and reserved words agree. The framed version
returns all original resources. It never allocates a second physical
fraction or assumes another reservation is disjoint.

`wp_write` uses the actual native conditional event rule, including its
held-snapshot readback proof and exact reservation/power/trace updates.
The pin payer is executed inside the successful event's later. A blocked
write preserves its state, snapshot reservation and complete payer; a
commit appends the authored snapshot, clears the local reservation and
advances the local view to the new log length. The continuation receives
all new pins, the exact history index `time-1`, positivity of `time`, the
cleared reservation and the matching view receipt. `step_inv` independently
exposes the blocked and commit arms with all effect/frame equations.

`write_ram_eq` is an equality of the actual generated conditional builtin
and its event tree, retaining every raw response arm. Every `.Ok` payload
maps to true and the actual `.Err ()` maps to false. `wp_write_ram` derives
the completed true continuation from the native event theorem; it does not
assume an SC success response or eventual commit. The general present-
payload V1 builtin corollary retains every other request field. Dependent
event index eight remains distinct from generic request-size metadata;
`conditionalRequest` has the exact source size eight and normal-strength
exclusive access kind.

Source scope: `HartMStore.v:757–802`, `PtTreeAdue.v:1213–1237`, and the
write-node use in `HartSKpt.v:759–906` at xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`; actual generated
`PhysMemInterface.write_ram:292–326`, with existing native MemoryWriteWP
and Reservations semantics. This is the direct physical pin/event bridge.
Shared KPT accessors, checked supervisor prefixes, actual translation,
canonical tree agreement and the complete read-update-write walk remain
separate. The model-to-Rocq correspondence limitation is unchanged.

Final Link build passed **462 jobs** (Proofs 1.1 s, Link 817 ms). A fresh
physical-origin audit checked **75 declarations** across all four modules,
including private helpers, transitive types, opaque bodies with
`allowOpaque := true`, and constructors. Only `propext`, `Classical.choice`
and `Quot.sound` occur; no unsafe/partial logical dependency and **zero
excluded companions**. No native decision tactic or custom axiom is used.
Initial proof elaboration failures were corrected before this validation.
Evidence: `/tmp/xv6-lean-research/TsoPinnedWriteWPAudit.lean`,
`tso-pinned-write-wp-build.log`, and `tso-pinned-write-wp-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
