# Native lock rank and held-set review

The coordinator read all six modules and the complete pinned LockRank.v and
LockSet.v sources. The 405-job build passes. A fresh independent audit checks
all 193 logical declarations and their opaque-body, type and constructor cones,
with only the standard three axioms. One safe total-recursion compiler companion
is excluded as a root; no unsafe/partial dependency occurs in a logical cone.

The carrier contains arbitrary lock names. The exact fifteen-entry rank table
and default zero are preserved; distinct names are not identified by rank.
Native Auth over the disjoint-set camera supplies exclusive singleton tokens,
authority agreement, fresh insertion and token-consuming deletion. The depth
predicate retains the exact set-cardinality bound. In particular, deleting an
owned member pays the decreased bound, while arbitrary releveling requires the
new bound explicitly. This does not assert a whole-kernel deadlock theorem.

Canonical wrappers select Era.Record.heldLocks for each CPU. Slot 26 extends
the current registry, with explicit old-slot capacities and preservation below
26; the lock-state camera stays at 24. Fresh empty allocation is available,
but the eight canonical boot names are not claimed allocated yet.

Approved as production-kernel prerequisites. Supervisor execution, TSO context
transport, interrupt ownership and the actual lock invariant remain separate.

Reviewed Lean source hashes (SHA-256):

```text
91ef39b97f2c103fad895bd410bb7d98cd8a79056cfc0da41cb597b763e409b9  MachCSL/Logic/LockRankDefs.lean
12d42989d3ff230d88c505dfcb7a14dd48af3e002ea2cd13da1d08b1eec5cdb6  MachCSL/Logic/LockRankProofs.lean
6375a8b1af0680a15329c7c1267097fcdd8fdc2d667322bc7fa7ff5b45220874  MachCSL/Logic/LockSetDefs.lean
c36d9cf5984c07d0743f81a93f1187f108d7f7d4cf65bfae44f6a03ec8e407fd  MachCSL/Logic/LockSetSpec.lean
3fd67a2a3827337c8cfc07f9f28027c823bcb762d4dcd0eca05b9cb2732065de  MachCSL/Logic/LockSetProofs.lean
22b5ffd1133525e291457f781dcc398c37e3cfe5da4a04884c6d90b1e8a2c35d  MachCSL/Logic/LockSetLink.lean
```

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
