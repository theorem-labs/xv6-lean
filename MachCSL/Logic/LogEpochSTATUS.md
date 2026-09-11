# Native journal epoch and append receipts

LogEpoch{Defs,Spec,Proofs,Link} implements the native fragment layer from
LogDefs.v:475–550 at the pinned paper source: epoch lower bounds and persistent
receipts that a signed block was appended in a specific epoch. It also provides
isolated native monotone epoch update and genesis allocation, corresponding to
the camera operations used in LogInv.v:1892–1926 and the genesis values in
LogDefs.log_free_tok.

The epoch authority and lower bound use the existing MonoNat camera at slot 3,
with explicit runtime names. They are not identified with the machine's log
length, generation counter or any inode observation counter. The append camera
is Auth over the finite set of Nat-epoch/Int-block pairs at new slot 34.
Authority and singleton fragments are real native Iris ownership. A receipt
retains both indices; old-epoch receipts remain valid and persistent.

The native laws preserve epoch authority when extracting a lower bound, derive
bounds from actual authority/fragment validity, and mint the zero anchor via
the camera unit update. Append mint adds one pair to the same authoritative
set and returns its persistent singleton. Existing membership can be reminted
without changing the authority. None of these primitives establishes that an
old receipt belongs to the current operation or header: log_use_group and its
operation-map/epoch invariant remain separate.

The isolated genesis allocator creates an epoch authority at ONE and an empty
append registry, retaining an arbitrary frame in the supplied GF. It does not
initialize a whole log, allocate InvGS, replace existing names, or supply the
lock, operation-map and transaction-map pieces of log_free_tok. The monotone
update requires old ≤ next; preserving the full log invariant at a commit is
not hidden in that camera rule.

The registry extends LogTx only at 34; explicit native capacities retain every
previous slot, including transaction 33, type 32 and shared mono-nat 3. All
slots 35 onward remain unchanged. Generic laws are instantiated by registrySpec
without assumed subordinate implementations.

Validation: LogEpochLink passes 472 jobs (proofs 909ms, link 1.2s). Independent
source and full opaque/type/constructor review is recorded in
repository docs/reviews/log-epoch-peer-review.md. These component receipts are
prerequisites for the inode's observation-epoch receipt; they do not prove
journal commit, crash consistency or initialization of the six whole-xv6 roots.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
