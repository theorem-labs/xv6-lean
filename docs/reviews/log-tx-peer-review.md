# Independent native transaction-pin review

Result: PASS for the four frozen `LogTx{Defs,Spec,Proofs,Link}` modules,
including the final native full-token mint/retire and cardinality additions.
The sail-audit agent owns this report only. No production files were changed.

Read the complete pinned `TxPin.v`, the `ln_tx` camera in
`Xv6Cameras.v:420–427`, empty allocation in `LogDefs.v:591–602`, the source
split/join/full-token laws in `LogInv.v:832–900`, and transaction insert/delete
in `LogInv.v:1664–1697`. Compared those contracts with all definitions and
proofs in `LogTx{Defs,Spec,Proofs}.lean` and the native Iris GhostMap APIs.

The carrier is the actual native ghost map from transaction Nat to Unit,
using a finite extensional tree map. The pin contains ownership at a fixed
transaction and positive `Qp` share, not an existentially selected transaction
or a pure assertion that a transaction is open. The name is explicit. This
implements the source `ln_tx` component without inventing the rest of the log
name record or a complete log invariant.

Optional pins preserve exact `none = emp` and `some (t,q) = tx_pin t q`
semantics. The general finite-map pin ledger separates rows by their own
keys while preserving each row's transaction/share payload. Different park
keys may refer to the same transaction, as in the source; no deduplication or
single-valued per-inode replacement was introduced. Generalizing source
countable-key gmaps to any `LawfulFiniteMap` is justified by the exact lookup,
finite big-separation, and extensional map equality laws used in the proof.

The empty-authority refutation uses actual authority/fragment lookup to obtain
an impossible present entry in the empty map. The optional and ledger forms
reduce to that contradiction. The ledger proof checks an arbitrary present
row and concludes extensional emptiness; it assumes no unproved cover or
external transaction registry. `authQ`'s broader DFrac interface is supported
by the native generic lookup theorem, while the exported empty-authority and
mutation rules require the source's full authority.

Splitting and joining keep the exact transaction and use the equation
`q = q1 + q2`, with both shares positive by the `Qp` carrier. They invoke native
fractional GhostMap ownership; no fractional resource is copied. Empty
allocation creates a fresh ghost name in the existing GF and retains the
supplied arbitrary frame. Insertion requires an absent key and returns full
entry ownership. Deletion consumes that full entry share and preserves the
other map entries. Neither update replaces authority with a fresh allocation.
These are isolated native operations, not complete begin_op/end_op proofs.

The raw-element bridge is a definitional equality with native element
ownership, and the Spec now exports the general finite-ledger no-ops law.
The Link inserts the exact transaction camera at slot 33, proves all prior
slots 0–32 and all later slots 34 onward unchanged, and carries explicit
existing capacities. No camera aliasing or hidden second world appears.

The added `log_tx` existentially hides the full token's transaction ID, exactly
as source `LogInv` does. Mint chooses a fresh finite-map key and returns the
updated authority plus that full token. Retire opens the token, derives actual
row presence and deletes that row. It does not invent a relation between the
transaction identifier and an operation-budget ledger key. `empty_of_ops`
retains the explicit cardinality equality and empty operation-map hypotheses.
These additions match the source laws; their surrounding begin_op/end_op and
full log-state invariant remain outside this isolated camera layer.

Fresh validation: the independent physical-origin audit
`/tmp/xv6-lean-research/LogTxPeerAudit.lean` was replayed against the final
frozen built modules. It traverses types, opaque bodies and datatype
constructors, and rejects nonstandard axioms, unsafe/partial code and initial
snapshot allocation dependencies. All 159 logical declarations pass with
only `propext`, `Classical.choice`, and `Quot.sound`; zero roots are excluded.
The owner's final four-module target passed 468 build jobs.

A scratch-only compilation during the append found a named-argument typo
(`get?_fresh` expects `H`, not `h`); the owner corrected it before this freeze.
No semantic change or reviewer production edit was needed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
