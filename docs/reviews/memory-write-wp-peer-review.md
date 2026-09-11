# RAM write WP independent peer review

Reviewed the frozen `MemoryWriteWP{Defs,Spec,State,Proofs,Link}.lean` and
status against pinned `HartEvents.v:299–377,492–573,797–892`, its
`wstore_tv` definition, and the actual RAM `MemWrite` branch in
`RiscvLang.v:875–913`. I also checked the Lean `NodeStep`, `writeBack`,
reservation, store-window, native WP, and fixed-state interfaces used by
the implementation. Pin: `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
Result: pass; no correction required for the stated event-rule scope.

The generic rule's explicit present-payload and non-device premises match
the actual generated event representation. The complete dependent request
is preserved; there is no added generic width/alignment/exclusive premise.
The absent-payload distinction is correct: the native builtin returns
purely without emitting a write, whereas a forged absent-payload event
has no live successor. MMIO stays outside the rule.

`writeState` matches the actual successful node successor: the modular
byte write and one hart-authored snapshot append occur together, the own
reservation becomes absent, and the actual access classifier determines
whether the own view stays unchanged or reaches the appended log top.
`written_step`, `blocked_step`, and `step_inv` tie this state to actual
machine constructors and exhaust every live successor. A blocked write
keeps the whole state, event, continuation and own reservation; the guarded
Löb proof retries without consuming the callback. The dead-generation arm
uses the real dead transition and preserves the whole trace/state.

The callback has the source's top-to-empty update, later, and empty-to-top
restoration order. It owes the precise new global-register/full-heap/device
bundle and TSO interpretation, then a continuation consuming the cleared
reservation and exact resulting view receipt. The rule itself frames the
remaining era/fixed resources and pays the reservation authority update.
`writeState_reservationsOK` proves other held snapshots survive from the
actual footprint's disjointness with the union of other reservations.
It does not assume those other snapshots are pairwise disjoint. The
observation interpretation is restored using an actual silent write step.

The conditional specialization adds exactly the source bound `n < 2^64`
and snapshot fragment. It derives the current-read equality from the
native authority-backed held-snapshot contract; it does not assume the
old RAM word or require a particular access classifier. The generic write
rule keeps arbitrary modular widths. The ledger specialization separately
requires `n ≤ 2^64`, extracts real full old ledger cells, and applies the
proved `TsoStore.StoreSpec.window` update. It returns the new timestamped
window and exact authored message receipt. The closing callback still
owns application invariant restoration; it is not a supplied callee WP.

`nativeContracts` discharges the store, views, reservation and held-snapshot
contracts using existing implementations. The concrete link uses the same
`FsLink` machine capacity and supplied invariant world, with no new camera,
byte authority, name allocation, or abstract preservation hypothesis.
These are direct native event rules rather than an implementation of the
entire source SWP/context API; generated AMO execution and a complete lock
invariant remain subsequent composition work.

Independent validation:

- `python3 tools/lake.py build MachCSL.Logic.MemoryWriteWPLink MachCSL.Logic.FsViewLink`:
  passed 458 jobs.
- `/tmp/xv6-lean-research/MemoryWriteWPPeerAudit.lean`: all 58 physical
  logical declarations from all five modules, including private helpers,
  passed the axiom allowlist and recursive type/body dependency check.
  Only `propext`, `Classical.choice`, and `Quot.sound`; no unsafe/partial
  semantic dependency and zero excluded runtime companions.

This reviewer did not implement the reviewed write modules. The reviewer
previously implemented the held-snapshot/exclusive-read dependency and
parts of the underlying memory/ghost library; that authorship is disclosed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
