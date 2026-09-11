# Native context pin mint boundary

The coordinator approved the definitions and fourteen native contracts before
implementation. All fourteen now have kernel-checked native proofs and a
concrete Link.
It follows the complete pinned `CtxPinMint.v` (350 lines) and `KptPublish.v`
(551 lines), at xv6iris arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The owned prefix is `MachCSL.Logic.ContextPinMint`. Defs and Spec are separate;
PureProofs, LedgerProofs, BootProofs and Proofs construct the obligations;
Link constructs `nativeSpec` at any supplied capacity, `registrySpec` at the
existing context registry and `eraSpec` at any complete era capacity.
Existing frozen files, registry slots and umbrellas are unchanged.

## Source mapping and exact distinctions

| Contract | Pinned source | Exact boundary |
|---|---|---|
| `timestamp_bound` | CtxPinMint59–78 | Any fraction/payload; actual timestamp authority and Latest imply a legal log position. |
| `own_bound` | CtxPinMint81–140 | `ownPub (hartAgent cpu) g.log ≤ g.views cpu`, clean/dirty context bit and the actual context authority. |
| `ledger_mint` | TsoCtx4604 (`ledger_pin_mint`) | Full existing byte/timestamp ownership; `time ≤ bound` and membership allow the same timestamp entry's payload to change from None to a pin. |
| `view_now` | CtxPinMint334–348 plus native `viewLB_llb` | Current hart view receipt and its log-length lower bound, preserving the TSO interpretation. |
| `log_now` | TsoCtx1664 (`tso_interp_loglen_llb`) | Log-length lower bound only. |
| `byte`, `bytes`, `word` | CtxPinMint147–225 | Own-publication drain; pins at the current hart view; same full heap, TSO and context token returned. |
| `byte_top`, `bytes_top`, `word_top` | CtxPinMint256–324 | No drain; pin at log length; no view receipt. Byte form needs no context token, while run/word forms thread it unchanged. |
| `byte_boot`, `bytes_boot`, `word_boot` | KptPublish330–463 | Hart agent zero; each byte has its own floor and a zero/own-message/view anchor. The common upper bound is log length. |

The boot word is the source aligned slot's physical byte component,
generalized to arbitrary offset-indexed allowed sets. Specialization to the
canonical PTE allowed sets and the recursive tree conversion remains the next
publication layer. `pinnedWord` and `bootWord` preserve the input alignment;
byte runs retain arbitrary Nat lengths and modular addresses without adding
an injectivity or no-wrap premise. Full byte ownership remains required.

`Drained` never means the whole log is visible. For example, another hart may
have later messages. The boot arm does not assume `Drained` at all. Its
source construction chooses floor=time, bounded by log length. At zero it
uses the zero anchor. A positive clean or below-context-bound byte uses a
view receipt; a dirty own-message byte uses its actual history receipt.
The dirty-set property alone says nothing about whether that message wrote
the address: Latest plus timestamp/heap agreement and the matching log index
must establish that part of the own-message anchor.

## Actual native dependency route

`Capacity` and `Names` reuse `TsoContext`/`TsoStore`. The heap's byte and
metadata names, timestamp name, log authority, log-length authority, views,
and dirty context names remain unchanged. `heapAt` retains the entire native
gen_heap, including metadata. `tsoInterpAt` retains the actual state memory,
image, log, views and timestamp-map validity ties. No physical bytes or state
are changed by minting the ghost pin.

The source's low-level operation is `TsoCtx.ledger_pin_mint`; neither the
pinned source nor current Lean tree has a file named `TsoPinnedCamera`.
The necessary current native APIs are present:

- `Tso.timestamp_lookup`/`timestamp_update` perform the held full-fragment
  timestamp update at the existing authority.
- `Heap.valid` and the timestamp validity tie identify the actually owned
  byte's Latest witness. `Tso.pinOK_mint` supplies the new pin condition.
- Rebuilding timestamp-map validity after insertion preserves domain and
  every other timestamp entry; None's other payload fields remain None.
- `Tso.Views.viewAuth_valid`, `viewLB_get`, `viewLB_llb` and `llb_get` support
  the exact view and length receipts without advancing actual views.
- Existing dirty-set lookup, finite separating-conjunction extraction and
  actual log lookup support the own-publication and boot-message arguments.

There is no missing camera or known unconstructible native premise. The completed proofs establish the own-message index bound, held-authority
None-to-pin map update, clean/dirty routing, finite byte-run folds and word
packaging. In `bytes_boot`, the induction carries each original floor, its
bound proof and its original `slotAnchor` unchanged into `slotBytes`; no
anchor is replaced by a current-log-top view assertion. No Initial allocator, fresh context, pure pin-validity oracle,
new state authority or fixed physical word is admitted by the signatures.

## Validation and next gate

The initial `ContextPinMintSpec` build passed (344 jobs). The completed
`python3 tools/lake.py build MachCSL.Logic.ContextPinMintLink` passes
(434 jobs). All fourteen approved signatures remain unchanged.

The full physical-origin audit covers all 62 declarations in all seven modules,
including private/generated helpers, types, opaque bodies and datatype
constructors. Only propext/Classical.choice/Quot.sound occur, zero exclusions;
there are no unsafe/partial or Initial dependencies in the logical cones.
Six supplementary kernel checks cover foreign/own publication index behavior,
the unchanged other payload arms, an exact one-byte boot floor/anchor, and the
empty boot run.

Evidence under `/tmp/xv6-lean-research/`:

- `context-pin-mint-signatures.log`, `context-pin-mint-build.log`.
- `ContextPinMintOwnerAudit.lean`, `context-pin-mint-owner-audit.log`.
- `ContextPinMintChecks.lean`, `context-pin-mint-checks.log`.

Next is specialization to canonical PTE allowed sets and recursive UTier→KTier
page/tree publication. This prefix establishes its actual physical pin-mint
prerequisite, not that tree publication, source boot reachability or a complete
translation WP.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
