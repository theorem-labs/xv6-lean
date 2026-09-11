# Native journal transaction ownership

LogTx{Defs,Spec,Proofs,Link} implements the paper's actual ln_tx ghost map
(Xv6Cameras.v:427), TxPin.v vocabulary and ownership laws, LogDefs.v:591,
and the transaction mint/retire/cardinality steps of LogInv.v:1664–1713.
The native camera is an authoritative finite Nat-to-unit map with positive
fractional fragments. Every predicate takes the actual transaction ghost name;
optional pins preserve both transaction identity and share. Finite pin ledgers
are generic over their original key type and lawful finite map, not restricted
to transaction indices or replaced with another authority.

Native lookup, fraction splitting/rejoining, empty-authority exclusion and
optional/finite-ledger emptiness consume the actual Iris ownership. Empty
allocation produces a fresh name in the supplied world and retains its frame.
Insert and delete update the same authority; deletion requires a full pin.
The anonymous log_tx existentially hides the identifier. Mint chooses a fresh
Nat in the finite map and returns its actual full token; retire identifies and
deletes the presented token's own row. It does not equate that identifier with
an independently indexed operation budget. Empty-of-operations uses the source's
explicit map-size equality. No operation-map invariant is silently assumed.

Registry slot 33 extends IcacheTypeGhost's registry, with explicit unchanged
capacities for every earlier slot, including type 32, reference ledger 31 and
count/mirror/window pins 28–30. Slots 34 onward remain unchanged. This prefix
constructs no alternate Iris world and allocates no full log invariant.

Validation: LogTxLink builds successfully (468 jobs). An independent source and
full opaque/type/constructor audit is recorded in docs/reviews/log-tx-peer-review.md.
The complete LogRes, operation budgets, shelters, logged block resources,
commit/crash invariant and begin_op/end_op machine-code proofs remain open.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
