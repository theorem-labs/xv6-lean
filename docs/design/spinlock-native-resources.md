# Native resource protocol for the two-hart gate

Author: OpenAI Codex subagent `lean_logic_audit`. The following design is now
implemented by the nine SpinlockProtocol modules and independently reviewed by
the coordinator and artifact agent. See SpinlockProtocolSTATUS.md for validation.
The complete two-hart integration gate remains open.

The resource transfer occurs at the successful conditional-write event whose
reserved old word is zero. The exclusive read returns its observed word and
an exact reservation, leaving the free counter resource inside the invariant.
The invariant is closed before the next event. This matches the operational
holder window and needs no duplicate reservation authority.

## Carriers and names

Component entry files: `MachCSL/Logic/SpinlockProtocol{Defs,Spec,Proofs,Link}.lean`
and `SpinlockProtocolSTATUS.md`, with helper modules under the same prefix if
needed. Reuse the actual addresses and complete request constructors in
`Machine.SpinlockAccess`, rather than restating their metadata. All data words
are `BitVec 32`; acquisition and storage positions are `Nat`.

```lean
structure Capacity (GF : BundledGFunctors) where
  machine : MachineInterp.Capacity GF
  lock : Lock.Capacity GF

inductive Phase where
  | idle
  | reserved (old : BitVec 32)
  | held (acquisition : Nat) (counter : BitVec 32) (timestamp : Nat)
  | loaded (acquisition : Nat) (counter : BitVec 32) (timestamp : Nat)
  | stored (acquisition : Nat) (counter : BitVec 32) (timestamp : Nat)
```

Runtime parameters are the existing fixed machine names, generation, complete
era record, a fresh lock ghost name `γ`, a namespace `N`, and the client CPU.
No additional camera is proposed. The native link uses the actual lock product
at slot 24; it can instantiate the generic capacity at `Lock.registry` or its
preserving `FsTop.registry` extension. The namespace must be a disjoint sibling
of the gate's observation/UART/PLIC namespaces when those are assembled.

Define `wordAt a v t` as the existing full
`TsoStore.storedWindow` at size four, using `capacity.machine`'s existing
physical byte/timestamp cameras and era names. It retains both full byte and
full `payNone` timestamp fragments at a common exact position. Boot starts both
words at position zero; all subsequent program stores return this same form.
Heap metadata and every unselected memory cell remain framed.

## Invariant body and held resources

The invariant body is exactly the following restricted gate resource:

```text
∃ B lockTime,
  (wordAt lock 0 lockTime ∗ Lock.authAt γ none B ∗ Lock.fragAt γ none B ∗
     ∃ counter counterTime, wordAt counterAddress counter counterTime)
  ∨ (∃ owner, wordAt lock 1 lockTime ∗
       Lock.authAt γ (some(owner,false)) B)
```

The full authority remains only inside this invariant. A failed swap writes
one while keeping the existing owner and acquisition position; neither the
latest lock timestamp nor its latest author is identified with the holder.
The `false` marker keeps the source's owner-field-not-written state throughout
this simplified program, which has no `lk->cpu` store. It is not repurposed as
a pending-read flag. The full counter ledger and matching free lock fragment
are present only in the free branch. In the held branch, the client owns them.

`won cpu B` contains the matching
`Lock.fragAt γ (some(cpu,false)) B`, the actual hart view receipt at `B`,
`0 < B`, and the persistent authored history receipt at index `B-1` for the
winning four-byte write of one. The callback chooses `B = oldLog.length+1`
from its actual state parameter and new-message receipt. This records the
acquire event's real position; subsequent spinner writes do not replace it.

Phase payloads:

- `idle`: `True`.
- `reserved old`: the pure fact `old = 0 ∨ old = 1`, with no counter or holder
  resource. The exact snapshot stays in EventPlan's separate reservation
  fragment, never duplicated into this payload.
- `held B v t` and `loaded B v t`: `won cpu B ∗ wordAt counterAddress v t ∗
  ⌜t ≤ B⌝`. The first permits the counter read; the second permits its store.
- `stored B v t`: `won cpu B ∗ wordAt counterAddress v t`. There is deliberately
  no `t ≤ B` assertion: a plain counter store need not advance the hart view
  to its own new timestamp. No later counter read is enabled in this phase.

`resource ... phase` also includes the persistent lock-invariant handle and
actual generation certificate. Including the certificate here gives the
plain-read resource callback the capability to open the matching live era
from `powerInterp`; the separate fold certificate can be shared because it
is persistent. It adds no second era or physical authority.

## Exact relation and callback interface

Construct `relations : EventPlan.Relations Phase` with these actual requests:

| Before | Event | After |
| --- | --- | --- |
| idle | exclusive read, `SpinlockAccess.readRequest .lock true` | reserved actual 0 or 1 |
| reserved 0 | present conditional write one, `writeRequest .lock true 1` | held B v t, with t ≤ B |
| reserved 1 | same write one | idle |
| held B v t | plain read, `readRequest .counter false`, returning v | loaded B v t |
| loaded B v t | `writeRequest .counter false (v+1)` | stored B (v+1) newTime |
| stored B v t | actual `Barrier_RISCV_rw_w` | same phase |
| stored B v t | `writeRequest .lock false 0` | idle |

All arithmetic on `v` is modular 32-bit arithmetic. This relation does not
claim a counter/release count equation. The generated instruction plan must
prove its real operand value agrees with the requested store value. The
underlying access-wrapper definitions remain general in all register operands.

Request eligibility identifies these concrete transitions, not hardware
success guards. Mode eligibility requires the exact reserved mode/snapshot
for both AMO write branches. Counter and unlock stores select ordinary mode.
This is the approved `writeModeEnabled` refinement recorded separately; it
prevents an unused ordinary-mode callback from incorrectly demanding an old
read value without its reservation proof.

Proposed Spec fields, with all callbacks free of callee-WP premises:

```lean
allocate : ∀ fixed gen era N,
  generationCertificate ... -∗ wordAt lock 0 0 -∗ wordAt counterAddress 0 0
    ={⊤}=∗ ∃ γ, inv N (body ... era γ) ∗
      (∀ cpu, resource ... fixed gen era N γ cpu .idle)

access : ∀ fixed gen era N γ cpu,
  EventPlan.Access capacity.machine fixed gen era cpu relations
    (resource ... fixed gen era N γ cpu)

holder_exclusive : ∀ γ cpu other B C,
  won ... γ cpu B -∗ won ... γ other C -∗ False
```

Allocation's universally available idle resource is persistent scenery only;
it creates no holder token or counter duplication. If using a direct invariant
handle-return API makes native proof composition clearer, derive this idle
family as a separate theorem with the same resources.

The callback implementation must prove the following concrete facts:

1. On exclusive read, extract full lock bytes from the opened invariant and
   use `MemoryExclusiveWP.heap_window_read` with the actual read bundle to
   obtain current zero/one. Restore the unchanged bundle, advanced TSO and
   invariant under the required guarded mask closure. Return only the
   reserved phase; the native leaf installs the exact snapshot separately.
2. On a reserved write, `WriteFact` supplies the actual current old bytes.
   Comparing them with the invariant's full physical lock ledger selects the
   free or held branch. This is not an assumed Boolean success result.
   Use `TsoStore` for the exact physical/TSO append. Zero acquires and transfers
   the counter; one preserves the other holder's authority/position and leaves
   its resources outside the invariant. Both clear the caller's reservation
   through the existing native leaf.
3. At acquisition, timestamp validity of a counter byte gives its timestamp
   at most the old log length (`TimestampOK` → `Latest` →
   `Memory.logByte_some_le`). The real conditional post-view is the new log
   length. This pays `t ≤ B` and the receipt needed for every later permitted
   plain-read view; no `.aq`-specific new semantics is assumed.
4. Plain counter reads split `storedWindow` into byte and timestamp windows,
   weaken the acquisition view receipt to `t`, and apply
   `TsoReadAt.power_read`. Cover every allowed view and every actual returned
   word, then recombine every full fragment unchanged.
5. Counter stores use the complete existing ledger update and retain its new
   timestamp, without claiming a view advance. Unlock uses holder/authority
   agreement, updates the actual lock word to zero, rejoins the free ghost
   roles and deposits the exact current counter ledger. The mask closes
   before the next event. The non-draining fence is the actual ghost-step
   identity, not a log-top drain.

Needed small helpers are bounded: full stored-word split/recombine,
current-word equality from the heap bundle, positive-width timestamp bound,
and a ledger update that frames the bundle's registers/devices while retaining
exact updated heap and TSO. These follow from the frozen ownership lemmas; they
must be proved, not become application assumptions. All invariant openings
follow the native top-to-empty / guarded empty-to-top protocol for one event.

## Source scope and remaining gate obligations

The source camera, acquisition-position agreement and non-owner latest-writer
issue are `WpLock.v:88–110,1329–1370`. The full source held word is
`lock_word_pin`/`lock_word_at` at 481–497; its timestamp payload carries a
value-set pin. The full holder predicates at 156–167 additionally carry a
context-indexed floor. `lock_pay`/`lock_pay_won` at 1242–1254 transport parked
contexts. This proposed machine-mode gate instead needs current exclusive
reads, full physical ledgers and actual hart receipts. It does **not** claim
to instantiate those richer source predicates or the complete xv6 lock API.
Those source payloads and context transport remain explicit later targets.

The annotated-pool `Covers` contract, holder-window exclusion, every generated
instruction/cycle plan, all device/power cases, fresh per-era boot resource
allocation and the interference witness remain separate proofs. The native
resource callback layer alone is not a closed two-hart gate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
