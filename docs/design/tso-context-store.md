# Native running-context store boundary



This proposed next slice implements the **registered physical context
store** `TsoCtx.v:2572–2587`, using the frozen native `TsoStore` update and
`TsoContext` resources. Source pin:
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The full per-byte helper and both
store gates at `TsoCtx.v:2327–2592` were read. No VA, SIE, stack, or software
WP assumption belongs in this gate.

Proposed owned files are new
`MachCSL/Logic/TsoContextStore{Defs,Spec,Proofs,Link}.lean` plus STATUS.
The frozen TsoContext modules need no change. Reuse their capacity and
names, including mono-nat slot 3 and dirty-set slot 5. No new camera or
registry slot is needed.

Define `physMap capacity names ξ map` as the finite native map separating
conjunction of `TsoContext.physPointsto ... (.own 1)` for every actual map
entry. Define a concrete `registerDirty D time new` using insertion of
`(time,address)` for every key of `new`, with a proved exact characterization:

```text
key ∈ registerDirty D time new ↔
  key ∈ D ∨ (key.time = time ∧ address ∈ dom new)
```

The public registered gate is:

```text
store names cpu ξ eraImage before after old new
  (sameDomain : TsoStore.SameDomain old new)
  (step : TsoStore.Transition before after new (hartAgent cpu)) :
  ⊢ TsoContext.heapAt capacity names before -∗
    tsoInterpAt capacity.tso names.tso eraImage before -∗
    ownContext capacity names cpu ξ -∗ physMap capacity names ξ old ==∗
    TsoContext.heapAt capacity names after ∗
    tsoInterpAt capacity.tso names.tso eraImage after ∗
    ownContext capacity names cpu ξ ∗ physMap capacity names ξ new
```

`Transition` constrains the exact image, one appended actual authored
message, decoded finite-map overlay, monotone CPU views and their actual
post-log bound. These are the source gate's equations, not a software
correctness callback. The ordinary-store corollary uses the exact
functional successor with `after.views = before.views`. Thus it requires
no artificial view advance; its view bounds follow from the pre-state TSO
interpretation and the one-element append. The general source gate also
allows the real monotone view change of an exclusive write; this does not
change the ordinary specialization's behavior.

The supporting registration theorem must expose the old and new dirty
sets explicitly. From the old full dirty authority, it returns full
authority for **exactly** `registerDirty D time new` and persistent
membership receipts for every new key. It does not remove old entries,
require pairwise distinct timestamps, or require fresh new keys. This
matches source `dset_insert`: membership may be re-minted monotonically.
The initial key set is arbitrary and finite.

Implementation decomposition:

1. Convert registered byte ownership to the existing full ledger map by
   retaining the byte and timestamp and forgetting only its clean/dirty
   justification fragment. The running token still owns the complete old
   dirty authority and all its justifications. No memory or timestamp
   resource is dropped or made read-only.
2. Before the store, derive `W ≤ before.log.length` from the running
   token's watermark receipt and the actual TSO log-length authority.
   This is a proved validity consequence, not an additional premise.
3. Invoke `TsoStore.nativeStoreSpec.update` once for the complete new map.
   It pays the full native heap and timestamp changes, actual single-message
   log append, and global view-authority update. In particular, the byte
   loop does not append one hardware message per byte.
4. Register all new `(before.log.length + 1,address)` keys. Preserve every
   old `dirtyOK` resource; construct every new one from the actual returned
   persistent log-entry receipt and its `hartAgent cpu` author. The old
   context bound B and existing CPU view receipt K remain unchanged.
5. Rebuild the running token at watermark `after.log.length`: old members
   are below the old W and new members have exactly this new timestamp.
   Obtain the new watermark receipt from the actual post-state TSO
   interpretation. Rebuild each context byte with its exact new timestamp
   and dirty membership. Return full heap metadata and all TSO resources.

An optional eight-byte/window corollary can be derived after the finite-map
gate is frozen. It must use the existing checked snapshot/finite-map bridge
and its explicit address-injectivity size bound; this is not a substitute
for the general finite-map theorem. The subsequent native memory-event
adapter will consume the actual ordinary write request and reservation
behavior through `MemoryWriteWP`, not assume an `Access` callback.

There is a deliberate scope distinction from the more general source
`ctx_store_free_ok` at lines 2430–2450. Its `phys_free` input admits arbitrary
old timestamp payloads; the existing `TsoStore.ledgerMap` and registered
context byte both require `payNone` on written addresses. The proposed
registered gate exactly matches `ctx_store_ok` and is sufficient for the
`mycpu` stack. It must not be advertised as the full visibility-free
`phys_free` gate. Supporting arbitrary old pin/window/release payloads
requires a separately reviewed extension of the native store payer and
its validity obligations. Off-address payloads already remain arbitrary
and are framed by the existing exact `TsoStore` theorem.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*

Implementation checkpoint: the registered finite-map gate, exact dirty-set
registration, unchanged-view ordinary specialization and all-view readback
are now implemented in `TsoContextStore{Defs,Spec,Proofs,Link}`. The final
target passed 429 build jobs; all 58 logical declarations passed the full
opaque-body audit. The arbitrary-old-payload free gate and subsequent
memory-event/stack/translation adapters remain outside this checkpoint.
