# TSO append-preservation review

Codex independently reviewed `TsoAppend{Defs,Proofs}` against pinned
`TsoMemPa.v` and the pure update used by `TsoCtx.ledger_store_ok:3951` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The review passes without requested
production changes.

The window, release and word-pin frame laws match source
`win_ok1_app_frame:1808`, `rel_ok1_app_frame:2153`, and
`pinw_ok1_app_frame:2583`. The shared lookup lemma excludes only the newly
appended message when it does not touch the selected address. Historical word
constraints, strict release-history bounds, represented entries, floors,
per-agent own-last bounds, and visibility obligations retain their original
witnesses. A message may touch another byte in the same window: the proofs
correctly preserve old-prefix facts and require absence only at the selected
address, just as the source does.

`timestampOK_append_frame` preserves the latest-byte witness and all four
payload implications, including function-valued window/history/predicate data.
Its memory premise is precisely equality at the selected untouched address.
It does not assume that framed entries have `payNone` or weaken their payloads.

`appendTimestamps` puts the replacement on the right of Std's right-biased
union. The lookup theorem proves that a present new byte gets exactly
`(oldLength + 1, payNone)` and an absent new byte retains the old timestamp entry.
The map-interpretation proof uses the actual functional byte overlay and exact
authored message; its touched branch obtains the latest timestamp from the new
append, while its untouched branch applies the complete frame theorem. The
domain theorem matches the same physical overlay. These pure statements may
add previously absent keys; the later ownership update must separately derive
or require the source's old/new domain and owned-cell constraints. They do not
claim that native ghost resources have already been updated.

Fresh independent physical-module-origin audit: 21 logical declarations in the
two modules, including private helpers, with only `propext`, `Classical.choice`,
and `Quot.sound`. The complete statement/proof dependency cone has no unsafe
or partial declaration, and no runtime companion was excluded. The owner's
334-job build and the independent imported-module check are green. Records:
`/tmp/xv6-lean-research/TsoAppendIndependentAudit.lean` and
`tso-append-independent-audit.log`. This reviewer changed no append proof file.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
