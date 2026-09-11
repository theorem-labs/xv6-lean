# Native ordinary context-word write event

`TsoContextWriteWP{Defs,Spec,Proofs,Link}` connects the registered context
word store to the actual present-payload eight-byte V1 write event and
native Iris WP. Source pin:
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
The relevant complete source boundary is `HartEvents.v:299–375` (write and
blocked retry), its `swp` wrapper at 797–838, and
`TsoCtx.v:2572–2592` (registered physical store). The existing native write
state, callback, reservation and full power/era update implementations were
also inspected before implementation.

| Obligation | Native implementation |
|---|---|
| Exact successful memory/log/view/reservation and remaining state fields | `Effect`, `write_effect` |
| Ordinary unchanged-view receipt and all-view identity | `ordinary_view`, `write_views` |
| Actual finite-map registered-store successor | `write_transition` |
| Complete blocked-or-successful live event inversion | `step_inv` |
| Full registered context payer and updated bundle restoration | `bundle_store` |
| Native ordinary present-payload write WP | `wp_write` |
| Explicit normal access kind | `wp_write_normal` |
| Actual present-payload builtin emission | `wp_write_builtin` |
| Constructed contract with all native dependencies discharged | `Spec`, `actual`, `nativeSpec` |

The theorem takes an explicit `WriteRequest 8`, with present new value,
non-device address, and nonexclusive access kind. Inputs are exactly the
real generation certificate, running context, full old aligned context
word, and the hart's reservation fragment at arbitrary `rr`. No caller
supplies a resource-access callback, successor-validity oracle, pristine
old bytes, assumed old readback, reservation-disjointness fact, or software
correctness theorem. The normal-kind wrapper specializes the general
nonexclusive theorem to explicit `AV_plain`/`AS_normal`.

The existing native write event rule handles every actual successor. When
another hart reserves an overlapping byte, the event retains the same
state, expression, reservation `rr`, and unopened callback, and retries
through the already proved guarded loop. The new adapter does not force
immediate success or assume fairness. Dead-generation behavior is inherited
from the native rule.

On a successful step, the event opens the complete live era and hands the
adapter its exact register/heap/device bundle and TSO interpretation. The
adapter first changes the mask and crosses the event's **later**; only then
does `bundle_store` invoke `TsoContextWord.ordinary`. `write_transition`
proves the actual functional successor is exactly the registered finite-map
store: `windowMap_decode` identifies the eight written bytes with the
actual snapshot, `writeBytes_overlay` identifies the memory overlay, and
ordinary access preserves every CPU view. The old/new window domains and
finite-window key injection are supplied by the existing checked word
store, with no global no-wrap assumption.

The payer appends exactly one actual message authored by this hart, updates
the native heap values and timestamp/log resources, retains complete heap
metadata, and registers every newly written byte in the same context's
dirty set while retaining all old dirty members. The bound/context names
are unchanged. The global register and device bundle is framed and rebuilt
at the actual successor, not duplicated or handed to the client. The
updated context word also supplies all-view readback through the existing
clean/dirty gate; no timestamp-zero conversion is used.

The adapter then restores the updated bundle/TSO under the correct mask.
The existing event rule pays its remaining full power/era/observation
bookkeeping, updates the own reservation from `rr` to `none`, and obtains
the ordinary receipt at the unchanged CPU view. The guarded continuation
receives the same running context, the full new word, reservation `none`,
and that receipt, and proves the real residual WP `k (.Ok none)`.
`Effect` and `step_inv` additionally expose the exact single authored append,
unchanged views/registers/devices/image/power/generation, and the reservation
update for every actual successful live event.

The dependent **event index 8** determines the eight-byte result/value.
The request's separate declared size, virtual address, translation, tag and
other metadata remain intact. The builtin bridge requires a present value
and proves the exact emitted event. It does not reinterpret the builtin's
absent-payload pure announcement as a memory write.

The context resources and capacity/name functions are reused directly from
`TsoContextReadWPDefs`; no camera, registry slot, or runtime ghost name is
added. This is the registered physical `payNone` input gate. Virtual-address
or kernel-tier interpretation, complete supervisor store instructions,
`mycpu`, and the broader arbitrary-payload `phys_free` interface remain
separate. This WP is a single memory-event rule, not a whole-instruction
atomicity claim or a termination theorem.

Validation: the final `TsoContextWriteWPLink` target completed **468 jobs**.
The fresh physical-origin audit checked **34 logical declarations across all
four modules**, including opaque theorem bodies, declaration types and
inductive constructors. Only `propext`, `Classical.choice`, and `Quot.sound`
occur; there are no unsafe or partial logical dependencies and **zero
exclusions**. The actual successor bridge, full context payer, native event
WP, builtin wrapper and constructed contract were also checked with
`#print axioms`. Raw evidence remains outside the repository at
`/tmp/xv6-lean-research/TsoContextWriteWPAudit.lean` and
`/tmp/xv6-lean-research/tso-context-write-wp-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
