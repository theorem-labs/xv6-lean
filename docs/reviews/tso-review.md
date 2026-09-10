# Independent initial TSO ownership review

PASS for the declared partial scope. No dropped source predicate conjunct,
spurious ownership premise, assumed functor instance or native axiom was found.
Reviewed all five production files and the cited pinned source definitions at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

Hashes:

- `TsoDefs.lean`: `c512fd712d0b3b2a323f77b2f925ccb16d83259f63fcdb12465aa507a49b7f78`.
- `TsoGhost.lean`: `9a35912cf4c8e75ef48852b8acac00712e17cbb2d602d3900ed4541ba03fba37`.
- `TsoPredicates.lean`: `7f7d45dda588c2227f6c046e1ca46110dc63b8623d34050160d327d5f2c331c6`.
- `TsoSpec.lean`: `250d9a61f70aee8f86411cd2a6b51dba2ae125b14522354af3b887e5df12e464`.
- `TsoOwnership.lean`: `58ad381be36c749bb916d3732688ca12c020c514080dc27e4278d21118efbc6d`.

Source comparison:

- `TsoMemPa.v:591–651`: `PinOK` and mint/append/frame/monotonicity laws retain
  quantification over every agent and every view above the bound. The latest
  timestamp being below the bound is required at minting, not incorrectly
  imposed as a permanent pin invariant.
- `TsoMemPa.v:1169–1171,1740–1798`: `Window` / `WindowOK` retain whole-window
  clear-or-author words for messages touching this byte at or above the floor,
  image coverage, the floor's complete clear word, and every per-agent own-last,
  visibility and clear-value condition.
- `TsoMemPa.v:2115–2152`: `ReleaseOK` retains strict-above-floor history coverage,
  real-message/author/whole-window evidence for every history entry, image
  coverage and each byte's floor value with no intervening write. No additional
  history ordering requirement was invented from the source comments.
- `TsoMemPa.v:2553–2579`: `WordPinOK` retains a predicate on whole word functions,
  positive width, per-byte identity, whole-window writes and the floor member.
  It is not replaced by independent byte sets.
- `TsoMemPa.v:2696–2753`: `Payload` has all four optional arms, and `TimestampOK`
  retains the current-memory/latest tie plus every arm's interpretation
  implication. Extensional finite byte sets replace stdpp gsets; addresses use
  the source 64-bit modular carrier.
- `RiscvPtsto.v:1050–1082,1551–1552` and `TsoCtx.v:2686–2745`: physical byte
  ownership includes the exact RAM interval. Pinned/window ledger predicates
  separate that byte ownership from timestamp-map fragments with the same
  fraction; map ownership uses real separating big conjunction and existential
  timestamps.

Resource and contract checks:

The resource algebras are native Iris `HeapView` over `Agree (DiscreteO V)`.
Inspection of installed `Iris.BI.Lib.GenHeap` confirms the byte slot matches its
value ghost map / `pointsTo`, while metadata resources are separate. Slot 0 and
slot 1 are explicitly certified in the Nat-indexed functor registry; the
injectivity lemma and unused-slot equality are proved. Runtime ghost names are
allocated by real ghost-map allocation and are not confused with slot indices.

The registry intentionally remains partial: it supplies neither full gen_heap
metadata nor source `tsoMemΣ`'s log-message map, per-agent view authority and
monotone dirty set (`TsoGhost.v:124–129`). It does not duplicate or assume the
shared mono-nat slot. These omissions are clearly recorded in `TsoSTATUS.md`.

`LedgerSpec` is independent of its implementation and contains actual native
Iris entailments/updates. `ledger_alloc` allocates authorities and full element
ownership; it does not assert arbitrary allocated maps satisfy a semantic
interpretation. Agreement, fraction splitting, exclusivity, lookup and update
use the real underlying ghost-map laws.

`physLedgerPin_read` needs both actual timestamp authority and the explicit
`TimestampMapOK` tie. Its conclusion follows by authoritative lookup and the
source `PinOK` implication. Owning a token alone never yields a machine read
fact. `physLedgerWpay_valid` has the corresponding complete window tie. These
are useful partial contracts, not the full source machine WP/store gates or
an established machine state interpretation. Window/release/word-pin lifecycle,
era/context allocation, richer TSO resources and cross-prover representation
correspondence remain outstanding.

An independent enforced `Lean.collectAxioms` audit passed all 243 declarations
in `MachCSL.Logic.Tso`, including definitions, instances, constructor equations
and proof exports. Every transitive axiom is among `propext`, `Classical.choice`
and `Quot.sound`. No native decision or custom axiom appeared. Scratch driver:
`/tmp/xv6-lean-research/TsoReviewAudit.lean`; log: `tso-review-axioms.log`.
No production edits were required.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
