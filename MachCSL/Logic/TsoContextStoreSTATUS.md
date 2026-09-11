# Registered running-context stores



The four `TsoContextStore` modules implement the registered physical
context store from `iris/TsoCtx.v:2572–2587`, source pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The complete source helper/store
section at lines 2327–2592 was inspected. This slice is a native resource
update and readback gate, not an instruction or whole-function WP.

| Source obligation | Lean implementation |
|---|---|
| Registered byte-map input/output | `physMap` |
| Exact old-or-new dirty set characterization | `registerEntries`, `registerDirty`, `mem_registerEntries`, `mem_registerDirty` |
| Monotone registration, including already present keys | `register_entries`, `register_dirty` |
| Registered input forgets to the physical ledger | `map_ledger` |
| Old dirty timestamps lie within the actual log | `watermark_bound`, combined with the existing running-token bound |
| New actual log-length receipt | `current_watermark` |
| Preserve old justifications; author every newly registered byte | `register_justifications` |
| Build registered output from stored value/timestamp/membership | `stored_context` |
| Exact source registered gate `ctx_store_ok` | `store` |
| Ordinary store with unchanged CPU views | `OrdinaryTransition`, `ordinary` |
| Constructed independent native contract | `Spec`, `actual`, `registrySpec` |
| Subsequent reads at every permitted view | `ordinary_readback` |

The gate consumes complete native heap and TSO interpretations, a running
context, and full registered bytes for an arbitrary finite old map. Its
pure premises are the actual same-domain and source successor equations:
unchanged image, one authored log append, the decoded new-map memory
overlay, and monotone/bounded CPU views. It returns complete heap metadata,
TSO interpretation, the running context, and all new registered bytes.
No resource callback or software correctness theorem is assumed.

The ordinary specialization replaces the view premises with exact equality
of all CPU views. It derives the post-log bound from the actual pre-state
TSO interpretation. It does not advance a view or add a fence. Fields
outside this resource interpretation are left unconstrained by the pure
transition; in particular this gate does not claim to update a register,
reservation, device, or power resource.

The implementation invokes the already proved full-map `TsoStore` payer
once, publishing exactly one actual message. A separate ghost-only fold
retains every old dirty entry and inserts every new address at the common
timestamp `before.log.length + 1`. It changes neither the context bound B
nor the view receipt K. The new watermark is the actual post-log length;
old entries are bounded through the old watermark and every new entry has
that new timestamp. The new dirty justifications use the payer's real
persistent authored-message receipt. The post-store readback theorem uses
the frozen clean/dirty load gate and preserves all its resources.

The registry is exactly `TsoContext.registry`, ultimately the held-lock
registry at slot 26; no new camera or slot is added. Mono-nat, dirty set,
log, byte and timestamp slots remain 3, 5, 4, 0 and 1. The complete source
heap metadata is retained throughout, and no writable resource is converted
to discarded ownership.

This implements the registered `payNone` input gate. It does **not** claim
the broader `ctx_store_free_ok` / `phys_free` gate accepting arbitrary old
timestamp payloads. Arbitrary off-address payloads already frame through
the existing store payer. Translation, virtual-address claims, stack
algebra, SIE capabilities, and a native supervisor function rule remain
separate tasks. The implementation follows
[`tso-context-store.md`](../../../docs/design/tso-context-store.md).

Validation: the final `TsoContextStoreLink` target completed **429 jobs**.
The fresh physical-module audit checked **58 logical declarations in four
modules**, including opaque theorem bodies and inductive constructors.
Only `propext`, `Classical.choice`, and `Quot.sound` occur, with no unsafe
or partial logical dependency. One generated runtime companion for total
list recursion was excluded as a root; the logical recursion and its full
cone were checked. The contract, store and readback proofs were additionally
checked by `#print axioms`. Raw evidence is outside the repository at
`/tmp/xv6-lean-research/TsoContextStoreAudit.lean` and
`/tmp/xv6-lean-research/tso-context-store-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
