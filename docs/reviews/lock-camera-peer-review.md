# Independent lock camera and top registry review

Reviewer: OpenAI Codex subagent `lean_logic_audit`, independently reviewing
`LockDefs`, `LockSpec`, `LockProofs`, `LockLink` and `FsTopLink`. Result:
**PASS for the declared camera and registry scope**. No corrections requested.
This is a separate review from the coordinator's `lock-camera-review.md`.

I compared the implementation with `Xv6Cameras.v:101–112` and
`WpLock.v:88–110,215–243,312–331` at arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The resource is the exact product
of exclusive-authoritative discrete `Option (CPU × Bool)` and `Nat`, with
both components at one ghost name. The source's acquisition position is
retained. Authority and fragment predicates existentially hide it only in
the source-style unindexed wrappers.

Both-field agreement follows from validity of the two native camera
components. Fragment and authority exclusion use native invalidity, and the
update consumes both matching roles before updating both components.
`update_state` first recovers equal hidden positions and retains that
position. Fresh allocation returns both roles; it discards no client token.
These proofs use native ownership allocation/update, rather than a separate
propositional ownership surrogate.

`acquire_at`, `set_cpu_at`, `clear_cpu_at` and `release_at` are correctly
limited to camera updates. In particular, `acquire_at` is not the full source
`lock_take`: the latter also needs an actual `ctx_floor` receipt and returns
`locked_pre`. The implementation and status explicitly leave floor/word-pin,
physical lock invariant and instruction/resource coupling unresolved.
The separate sleeplock camera is likewise explicitly unimplemented; no full
source `lockG` instance is claimed.

`LockLink` extends `FsLink.registry` only at slot 24 and `FsTopLink` extends
that result only at slot 25. Earlier and later slots are preserved by the
proved pointwise equations. I checked the reconstructed capacities against
the predecessor layout: bytes/timestamps 0–1, views 2–3, history 4–5,
registers 6, devices 7–9, reservations 10, observations 11, disk 12,
heap metadata 13–14, era registry 15, invariants 16–19, UART 20–22,
filesystem links 23, lock 24 and top inode map 25. Shared bytes and mono-nat
identities hold by reflexivity. The existing top-map camera and actual
invariant world are reused, with no placeholder slot.

Validation: rebuilt the frozen `FsTopLink` target (399 jobs). A fresh audit
selected all five modules by physical origin and traversed all declaration
types, bodies and constructor dependencies: 194 declarations, only
`propext`, `Classical.choice` and `Quot.sound`, no unsafe/partial semantic
dependency and zero exclusions. Scratch evidence is
`/tmp/xv6-lean-research/LockIndependentAudit.lean` and
`lock-independent-audit.log`.

This establishes the native resource algebra and its registry placement.
Concrete lock invariant allocation, operational protocol preservation,
resource transfer at the actual AMO/write events and mutual exclusion remain
separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
