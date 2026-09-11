# Native supervisor checked eight-byte store

The five `SupervisorWrite{Defs,Spec,Plan,Proofs,Link}` modules implement a
native WP for actual `checked_mem_write (Physaddr address) 8 new (Store Data)
PBMT_PMA Supervisor () false false false`. The public theorem owns four
fractional register cells, the actual running context, the old full word
and an arbitrary own reservation. It constructs the physical-access prefix
and uses the implemented context-write rule at the real memory event.
No access, state-update or whole-instruction correctness oracle is required.

Source pin: `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The exact source
store section and generated functions were inspected as recorded in
[`supervisor-write-boundary.md`](../../../docs/design/supervisor-write-boundary.md).
The generated model uses Sail source
`23dcf8fd923eb8a1958795393d2975632aa940b2` and free runtime
`28c729b5bb574ae7c32c13353403e57c575d85dd`.

| Source / actual path | Native implementation |
|---|---|
| `HartSMem.v:2930–3050` four-register store prefix | `Shares`, `footprint`, `cells`, `footprint_unique`; each share is independently arbitrary. |
| `Mem.lean:262–404` Data-store PMA and priority wrapper | `pma_store_plan`, `priority_store_plan`: real match, writable permission, false conditional assertion and aligned `CannotSplit` result. |
| `PmpControl.pmpCheck` under source supervisor TOR | Existing `SupervisorPmp.check_ram_plan` with `.store`, widened to the four-cell footprint. |
| `Platform.lean:711–717` writable MMIO predicate | `mmio_store_plan`: actual CLINT/signature checks and eager HTIF read, preserving the writable width test. |
| `PhysMemInterface.lean:292–326` ordinary present write | `request`, `write_ram_boundary`: complete exact request and both response branches. |
| `Mem.lean:534–582` singleton checked-write loop | `checked_boundary`, `add_zero`, `full_word`: arbitrary address and word, exact emitted event and complete residual. |
| Actual register-prefix composition | `Boundary`, `Boundary.bind`, `OneWrite.prefix`, `OneWrite.bind`; no alternative memory transition relation. |
| `HartEvents.v:299–375`; registered gate `TsoCtx.v:2572–2592,4346–4371` | `Boundary.fold` invokes actual native register rules and `TsoContextWriteWP.wp_write`; all heap metadata/TSO/context updates are discharged internally. |
| Full native physical-store contract | `wp_checked_write`, constructed `Spec`, `actual`, `nativeSpec`. |
| Actual live blocked/success cases | `event_step_inv`, `event_effect`, specialized from the completed context-write event theorems. |
| `Mem.lean:586–598` explicit-privilege callback wrappers | `value_priv_meta_eq`, `value_priv_eq`: checked equalities to the same program, reusing the existing Sail bind/pure law. |

The physical prefix performs five actual register reads from four distinct
registers: PMA once, PMP configuration twice, PMP address once, HTIF once.
It writes no registers. Pure alignment/split/order calculations yield one
iteration at offset zero, and the full 64-bit extracted payload equals the
original arbitrary word. PMA is checked before the loop's PMP check. The
successful PMA priority branch does not issue an additional PMP check.
The new store-specific PMA/MMIO proofs do not reinterpret the frozen read
permission predicates or change the existing physical plans.

The request has `AK_explicit` plain/normal access, VA none, the actual PA,
unit translation, declared size eight, payload `some new`, and tag none.
The dependent event width is also eight. `OneWrite` preserves the exact
residual for **every** V1 response: any `.Ok optionalBool` becomes the checked
result `.Ok true`; `.Err ()` becomes `.Ok false`. The write error is not the
read wrapper's exit behavior. The native owned-RAM proof establishes the
actual successful response `.Ok none`; the other syntactic continuations
remain in the checked decomposition.

The native rule derives alignment from the real full context word. Its
explicit pure premises are the source TOR RAM configuration, the eight-byte
RAM interval, disabled HTIF, the actual matching PMA region and its writable
permission. The source TOR package includes R/X as well as W; this store
checks W. There is no reset state, pristine old value, empty log, selected
read view, global reservation-disjointness or caller-provided `Boundary`
premise. The old word may already be dirty in the same context.

On a successful write, the existing native context gate updates the full
heap/metadata and TSO resources together, retains old dirty members, inserts
the actual newly authored byte keys, and returns the same running context
with the new full word. The actual state appends one writer-authored message,
keeps every CPU view unchanged, and clears only the own reservation. The
receipt is indexed by that unchanged event-time CPU view, not by the new log
length. The register cells are framed through the write and returned with
their original fractions.

When another hart's reservation overlaps, the actual node retries unchanged.
The native write rule retains the old word, running context, incoming
reservation and continuation until a successful transition. The new wrapper
uses that rule; it does not pay the store update on a blocked step. Power
changes are handled by the existing generation/dead-thread semantics.
This is native WP safety/partial correctness, not a termination guarantee.
`event_effect` describes a single actual write event, not an absence of
interleavings during the preceding register operations.

`SupervisorWrite` uses the same existing context/camera names as the read
and word layers. It adds no camera, registry slot, readonly conversion,
metadata allocation or duplicate authority. `Boundary` is local to the
write namespace; no active or frozen read module was changed. The
explicit-privilege wrapper equalities contain only actual pure callbacks;
they do not erase `mem_write_value`'s mstatus/current-privilege prefix.

Validation: the final `SupervisorWriteLink` target built successfully in
**529 jobs**. A fresh physical-origin audit checked **97 logical declarations
in all five modules**, including private helpers, full opaque theorem bodies,
types and inductive constructors. Only `propext`, `Classical.choice` and
`Quot.sound` occur; there are no unsafe or partial logical dependencies and
**zero exclusions**. The actual checked boundary, both-tail composition,
callback equality, native fold/public rule and event inversion also passed
explicit axiom queries. Evidence is outside the repo at
`/tmp/xv6-lean-research/SupervisorWriteAudit.lean` and
`/tmp/xv6-lean-research/supervisor-write-audit.log`.

`mem_write_ea` and effective-privilege prefixes, address transformation,
virtual translation, tier-mapped stack resources, fetched STORE execution
and `mycpu` remain subsequent proofs. In particular, the actual instruction
must retain its separate address-announcement/check stage. Conditional PTE
writes require `supports_pte_write`, an exclusive request, the actual
reservation snapshot and page-table/A-D/publication resources; none is
silently discharged by this ordinary Data-store theorem. Misaligned,
MMIO, AMO, acquire/release and arbitrary-old-payload visibility-free stores
also remain outside this checkpoint. Full Rocq/Lean event correspondence
is still a separate obligation.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
