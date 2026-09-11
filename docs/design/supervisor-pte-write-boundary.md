# Native conditional PTE write boundary

This is a design proposal. The first proposed implementation is a pinned
RAM-event adapter, using the frozen native pinned-store gate and actual
reservation/memory rules. A checked supervisor `write_pte_conditional`
wrapper and the shared KPT invariant accessor follow separately. None of
these are currently claimed as implemented by this document.

Source references are `.upstream/xv6iris/iris/` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`; generated references are the
repository's pinned `models/riscv/LeanPaperStock/` model. I read the exact
`PtTreeAdue.wpte_obl_at`, `HartSKpt.kpt_leaf_write_node`,
`HartMStore.wobl_ram_ledger_pin_exf`, actual generated update/read/write
wrappers, and the complete native `MemoryWriteWP` step and WP proofs.

## What the actual model proves about success

For a present-payload RAM write, `Machine.NodeStep` has precisely two live
arms: a blocked step leaving the entire state and residual program
unchanged, or a commit returning **V1 `.Ok none`**, appending the authored
snapshot, updating memory, and clearing this CPU's reservation. If the
request is exclusive, the view becomes the new log length. The own
reservation is not a hardware success-bit test in this source model.

`PhysMemInterface.write_ram:292–326` builds the exact conditional request:
`AK_explicit`, `AV_exclusive`, `AS_normal`, `va = none`, unit translation,
actual address, size eight, present 64-bit value, and absent tag. It maps
every V1 `.Ok _` to Boolean true and `.Err ()` to false. Thus actual RAM
commit implies Boolean true by the proved event inversion and wrapper
equation. It is incorrect to assume an SC result, replace the event with a
Boolean choice, or change its strength to acquire/release.

The reservation proves a different, necessary fact. Native
`MemoryExclusiveWPSpec.heldSnapshot` derives
`readBytes g.memory a 8 = some reservedWord` from the full actual power
interpretation, generation certificate, live-generation fact, and this
CPU's snapshot fragment. Its strict source bound `8 < 2^64` is discharged
arithmetically. It does **not** establish disjointness from every other
reservation: `ReservationsOK` states submap validity, not pairwise
disjointness. The adapter retains the native rule's guarded blocked retry
without adding such a premise. This is partial correctness and safety of
every allowed successor, not eventual-commit or fairness.

`Vmem.write_pte_conditional:226–229` calls the actual
`mem_write_value_priv` with `Store PageTableEntry`, Supervisor, PMA type,
and flags false/false/true. Checked register prefixes must separately prove
the absence of PMA/PMP/HTIF fault routes. Only after those proofs can its
completed return be `.Ok true`.

`update_and_write_pte:325–360` retains both recomputation branches after
the exclusive reread. If A/D is already sufficient, it returns the reread
word without a write and may retain that reservation. If an update is
needed, it performs the actual conditional write. Boolean false reaches
the actual `internal_error` at `sys/vmem.sail:226`; it is not a retry
algorithm. The native RAM theorem excludes that completed response from
the event semantics; the pure factorization still contains its false and
error residuals. No branch is removed to make the wrapper theorem easier.

## Proposed first owned files and public contracts

Proposed ownership is new
`Logic/TsoPinnedWriteWP{Defs,Spec,Proofs,Link}.lean`, with a local State or
Geometry helper only if needed, plus STATUS. Existing MemoryWriteWP,
TsoPinnedStore, and generated files remain unchanged. Use the current
machine capacity, ordinary native `InvGS_gen`, explicit era/generation,
actual `threadWP`, and the exact `MemoryWriteWP.writeState`; no new camera.

First prove a `bundle_store` adapter using
`TsoPinnedStore.StoreSpec.window`:

```text
writeBundle era g -∗ tsoInterpAt era g -∗
pinWindow a 8 physicalWord (own 1) floors sets ==∗
  writeBundle era (writeState g cpu req newWord) ∗
  tsoInterpAt era (writeState g cpu req newWord) ∗
  storedWindow a 8 newWord (g.log.length+1) floors sets ∗
  logElem g.log.length (snapshot a 8 newWord, hartAgent cpu)
```

Its only new pure content is membership of the new bytes in the existing
sets. `MemoryOK` and the actual state-transition equations are obtained
internally from the TSO interpretation and existing `writeState_transition`.
The bundle's global register and device authorities are framed; metadata,
timestamps, log and view ownership are updated together. Reservation,
generation, power and observation bookkeeping remains with the existing
native event rule. The source floor/set address bridge can be constructed
internally using modular offset `(address-base).toNat` and `j < 8`; it
does not need an added global no-wrap premise.

The direct resource rule should have this schematic public form (all
capacity, mask/world, and actual continuation arguments remain explicit):

```text
req : WriteRequest 8
req.value = some newWord
deviceAddress req.pa = false
accessExclusive req.access_kind = true
(∀ j < 8, nthByte newWord j ∈ sets j)

generationCertificate gen era -∗
resvFrag cpu (some (snapshot req.pa 8 reservedWord)) -∗
pinWindow req.pa 8 physicalWord (own 1) floors sets -∗
▷ (∀ time,
  storedWindow req.pa 8 newWord time floors sets -∗
  logElem (time-1) (snapshot req.pa 8 newWord, hartAgent cpu) -∗
  ⌜0 < time⌝ -∗ resvFrag cpu none -∗ viewLB cpu time -∗
  WP (k (.Ok none))) -∗
WP (.impure (.writeMem 8 req) k)
```

This is an event rule: the dependent event index is eight; the metadata
field `req.size` remains explicit and need not be silently identified with
that index. The concrete builtin request supplies `size = 8` by definition.
The fixed `req` theorem retains all other metadata. The caller's WP is
only the genuine post-event continuation, not a memory-success premise.

The conditional adapter internally uses the existing proved
`MemoryWriteWPSpec.conditional` and held-snapshot bridge. Add a separately
proved resource agreement lemma:

```text
ThreadLive g gen →
powerInterp g -∗ generationCertificate gen era -∗
resvFrag cpu (some (snapshot a 8 reservedWord)) -∗
pinWindow a 8 physicalWord dq floors sets -∗
  ⌜physicalWord = reservedWord⌝
```

Derive physical readback by projecting the pinned byte fragments to the
existing `MemoryExclusiveWP.heap_window_read`; combine it with
`held_snapshot_read` and injectivity of `Option.some`. Preserve the input
resources in a framed version. This provides the actual read-to-write
connection without assuming that a re-opened invariant's word equals the
earlier reread. It is not a proof that another CPU cannot cause blocking.

An optional generic present-write adapter can retain arbitrary incoming
reservation and actual `postView`, but the first milestone is the exclusive
eight-byte rule above and its exact `write_ram Write_RISCV_conditional`
Boolean-success wrapper. No checked `write_pte_conditional` or full walk
claim is attached to that first milestone.

## Shared read-then-write resources

The source shared-table proof (`HartSKpt.v:759–906`) opens `kptN` at the
write node, obtains its current leaf `q0`, full eight-byte pinned ownership,
and the per-byte persistent publication anchors. Canonical snapshot/map
agreement proves that the new word is an A/D variant of that current leaf.
The pinned store keeps the same floors and byte families; the path rebuild
wand and canonical-tree equality close the same invariant.

The earlier exclusive read must **close the invariant before returning**.
Only the actual snapshot reservation, persistent mapping/canonical claim,
and pure information about the reread word cross into the intervening
leaf checks. No full physical slot or invariant-open token is retained
across separate Sail events. At a subsequent write, the snapshot and the
newly opened full slot can also prove exact word agreement using the lemma
above. The source writer does not need this equality when canonical
membership already suffices, but the native bridge should expose it.

For this shared use, add a resource-only accessor adapter after the direct
rule is frozen. It may expose, at a single event mask, an existential
current word and per-byte floors with their full pinned window, plus a wand
which restores the caller's invariant from the new pinned window and
authored receipt. It must return the original bundle/TSO while extracting
the slot; the adapter itself performs the actual update. The restoration
wand returns a resource `Q`, **not a WP or an assumed successor-state
interpretation**. The final continuation consumes `Q`, the actual cleared
reservation, and the new view receipt. Such a generic accessor is useful
machinery; the eventual KPT theorem must construct it from the exact KPT
invariant, not leave it as a software-contract hypothesis.

Both exclusive-read branches remain visible. A blocked reread clears the
local reservation and retries with its invariant unopened; a completed
reread installs the actual snapshot and sets the view to the old log top.
Both write branches also remain visible. A blocked write retains its
reservation, pinned resources/accessor and state; a commit consumes the
old pin window, returns the new pins and clears the reservation. Stale
generation behavior uses the native dead-thread rule.

## Subsequent checked supervisor wrapper

After the event adapter, a separate `SupervisorPteWrite` plan must prove
the actual `mem_write_value_priv`/`checked_mem_write` prefix for
`Store PageTableEntry`, false/false/true, the source PMP grant, actual PMA
permissions/classification, aligned eight-byte physical PTE address, and
HTIF disabled. One partial fractional footprint covers the real PMA/PMP/
HTIF reads; preserve repeated reads and the exact singleton write-loop
result handling. Reuse existing pure supervisor prefix facts where their
access and flag parameters match; do not instantiate the ordinary Data
write rule with a changed request label. Its pure residual keeps all
Boolean/error branches and its native rule discharges only the actual
allowed responses.

The parent-owned `PteCanonical` contract supplies new-byte membership,
canonical equality and family preservation for all generated update
access kinds. The full KPT proof still needs tree path extraction/rebuild,
canonical agreement cameras, mapping claims, publication anchors, coherent
TLB hit/miss plans, and the actual leaf validation. The registered store
gate alone supplies none of these as assumptions disguised as proof.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
