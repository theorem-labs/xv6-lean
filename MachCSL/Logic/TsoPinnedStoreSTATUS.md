# Registered-pin store gate

Frozen `TsoPinnedStore{Defs,Spec,Pure,Proofs,Link}.lean` implements the
registered-pin map and window resource updates from `TsoCtx.v`, pinned to
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. This is a native basic-update
resource gate for explicit physical-state equations. It does not assume
or prove that a Sail event succeeds, and is not yet the conditional PTE
write WP or full KPT/Sv39 translation theorem.

`Capacity` and `Names` reuse `TsoStore`. The input `pinMap` is definitionally
the existing `Tso.pinMapOwn`, using full byte and timestamp fragments with
`payPin (sets a) (floors a)`. The public `StoreSpec.update` requires exactly
equal old/new finite domains, membership of every new byte in its existing
per-address set, and `TsoStore.Transition`: unchanged image, one actual
decoded-new-map message appended under the supplied Nat author, decoded
memory overlay, monotone CPU views, and post-log view bounds.

It returns the full gen_heap including its original metadata authority,
the complete TSO interpretation, the exact zero-indexed history receipt,
and full new pinned bytes with timestamp `oldLog.length+1`. **Each original
floor and allowed set is unchanged.** There is no conversion to `payNone`,
pin remint at a different floor, discarded physical ownership, assumed
registered-map lookup, or off-address payload restriction.

The map proof extracts all old existential timestamp witnesses from the
owned fragments using the already-proved finite collection lemma. Native
ghost-map validity ties them to the actual timestamp authority and recovers
their original payloads. The native byte and timestamp bulk updates retain
the same domains. The old registered-pin fact is passed internally to the
pure semantic update; the public gate has no additional premise for it.
The pure update uses `pinOK_append` at touched addresses and the complete
`timestampOK_append_frame` elsewhere. Window, release, and word-pin payloads
at untouched addresses survive along with byte pins. Exact map lookup and
untouched-entry equalities are separately proved.

| Source | Checked Lean counterpart |
|---|---|
| `pin_tm`, `pin_tm_lookup/empty/insert`, `TsoCtx.v:3517–3536` | `storeTimestamps`, lookup/domain/empty/insert laws |
| `ledger_store_pin_bytes`, `3538–3594` | `ledger_update`, using existing native bulk updates and exact old-payload recovery |
| `ledger_store_pin_ok`, `3596` onward | `update`, `timestampMapOK_store`, `timestampDomain_store` |
| `phys_ledger_pin_win_map`, `4190–4210` | generalized `window_map`, instantiated with the exact existential pinned-byte assertion |
| `ledger_store_win_pin_okf`, `4215–4250` | `update_window` with per-offset/address floor and set agreement |
| Uniform-floor `ledger_store_win_pin_ok`, `4253–4274` | specialization of `update_window` to constant floor functions |
| Source existential timestamp postcondition | `storedWindow_pin`, `storedMap_pin` |

The window theorem reuses the actual modular right-fold `windowMap` and
its checked decoder/snapshot equality. The source `n ≤ 2^64` injection
bound and the per-offset/address agreement premises remain explicit. New
membership is derived from actual finite-map entries, not from an unchecked
window lookup. The result retains the exact snapshot history receipt and
exposes each new timestamp; the forgetting lemmas recover the source's
existential timestamp form. Arbitrary word widths and the zero-length case
retain the existing `nthByte` and write semantics. No alignment or global
stack no-wrap premise is added by this algebraic gate.

The subordinate history append, monotone log length, and all-Nat-agent view
updates are the already-proved native camera contracts. `actual` discharges
all of them. `nativeSpec` uses the existing `FsBlockGhost` registry; checked
`heap_same` and `tso_same` equate its resources with the actual machine
capacity. No slot, name, generated model, frozen module, or dependency was
changed.

Validation: the full Link target built **503 jobs**, with final Proofs in
1.1 seconds and Link in 957 ms. A fresh physical-origin audit checked all
**43 declarations across five modules**, including private declarations,
types, opaque bodies using explicit `allowOpaque := true`, and constructors.
Only the permitted standard axioms occur; there are no unsafe/partial
logical dependencies and **zero exclusions**. Initial type annotations,
finite-map lookup spelling, and proof-mode reflexivity errors were corrected
before this build. No axiom, `sorry`, or native decision tactic was used.

Evidence outside the repository:
`/tmp/xv6-lean-research/TsoPinnedStoreAudit.lean`,
`tso-pinned-store-build.log`, and `tso-pinned-store-audit.log`.

The next operational boundary must derive the actual write successor
equations and reservation behavior from the machine rule, then combine
this gate with the independently implemented PTE canonical byte families.
The false/error residual of generated conditional write remains a separate
obligation; no success oracle is hidden in this resource layer.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
