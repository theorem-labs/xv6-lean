# Independent concrete spinlock protocol review

Codex independently reviewed all nine frozen `SpinlockProtocol` modules
(`Defs`, `Spec`, `Words`, `Init`, `Read`, `Store`, `Commit`, `Proofs`, `Link`)
and their status against the actual native `EventPlan` contracts, memory leaf
rules, invariant API and relevant pinned source lock definitions. No correction
was required for the declared machine-mode integration scope.

The source reference is `.upstream/xv6iris` arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`: `Xv6Cameras.v:101–112` and
`WpLock.v:88–110` provide the product of exclusive state and acquisition-position
cameras. The peer's code correctly reuses both components. `WpLock.v:1329–1370`
explains why the latest lock writer cannot be identified with the holder:
the reviewed failed-swap branch stores one at the new timestamp while retaining
the prior owner and winning position. The `false` marker retains its original
meaning (the owner field has not been written), consistent with this program's
absence of an owner-field store.

The complete source predicates are richer: `locked`/`locked_pre` at 150–163
carry a context floor; `lock_word_pin`/`lock_word_at` at 481–497 carry value-set
pins; `lock_pay`/`lock_pay_won` at 1242–1254 transport parked contexts. This
integration invariant deliberately does not implement or claim those full
kernel contracts. Its full physical words, exact timestamps and actual hart
receipts suffice for its narrower enabled requests.

The request definitions reuse the actual generated-access metadata. Mode
eligibility requires the exact four-byte snapshot and strict width bound for
both AMO write branches. Tracing `EventPlan.write_mode` reaches the native
conditional write rule, which obtains `WriteFact` from actual reservation
custody; it does not assume that the earlier read still holds. Ordinary stores
carry no such fact. In `commit`, full heap/lock ownership is compared against
the current read: a zero old value excludes the held invariant branch, while
one excludes the free branch. Reservation resources remain outside the
protocol payload and are consumed/reset only by the native event machinery.

Winning acquisition performs the proved full-metadata physical/TSO update,
chooses `B = oldLog.length + 1`, updates the actual native lock product and
transfers the full counter ledger. Timestamp validity of an owned counter byte
proves its time is at most the old log length. The returned payload contains
that bound, the actual authored-message receipt at `B-1`, a positive `B` and
the actual conditional-write post-view receipt. No publication position is
invented. Failed acquisition performs its real write but frames the owner's
authority and position, without taking the owner's counter or fragment.

Plain counter reads use the timestamp/view theorem at every allowed view;
the full byte/time resources and winning receipts are restored. The increment
stores `BitVec 32` addition by one and retains its actual new timestamp. It
correctly drops the earlier timestamp-at-most-acquisition condition: a plain
store need not advance the CPU view. Unlock checks holder/authority agreement,
stores zero, restores both free ghost roles and deposits the exact current
counter ledger. FENCE rw,w uses the actual non-draining identity resource
transition and mints no drain receipt.

The native invariant opening was checked against its exact mask contract.
Exclusive-read inspection restores the unchanged body and full state bundle
before its separate guarded event return. Write access opens from top to
`top \\ N`, enters the empty mask, invokes the physical/ghost commit only under
the required later, restores the intermediate mask and closes the invariant
before returning to top. There is no opening spanning separate AMO read and
write events. The unguarded `commit` helper is explicitly a body-level update;
the exported `write_access` provides its one-event guarded use.

Allocation consumes actual initial zero lock and counter windows, allocates
one native lock name and one invariant in the supplied existing world, and
returns only persistent idle scenery for arbitrary CPUs. It creates no holder
or counter duplicates. `actual` proves the complete callback specification
without external update/WP callback assumptions. `registrySpec` reuses the
existing `FsTop` registry and slot 24, preserving slots 0–25 and the supplied
native invariant instance.

Independent validation: `python3 tools/lake.py build MachCSL.Logic.SpinlockProtocolLink`
passed all 516 dependency jobs. A fresh replay checked all 199 physical-origin
declarations, including private/generated declarations, and traversed their
statement, proof-body and inductive-constructor cones. Only `propext`,
`Classical.choice` and `Quot.sound` occur; no unsafe/partial logical dependency
was found and zero declarations were excluded. Driver/log:
`/tmp/xv6-lean-research/SpinlockProtocolPeerAudit.lean` and
`/tmp/xv6-lean-research/spinlock-protocol-peer-audit.log`.

This is an independent review of the peer-authored protocol; the reviewer
authored some previously reviewed memory/resource dependencies and the access
wrapper plans it imports. The result proves native resource callbacks and
holder-fragment incompatibility. Annotated-pool coverage, cyclic generated
control, operational holder-window exclusion, the interference witness and a
closed two-hart adequacy theorem remain separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
