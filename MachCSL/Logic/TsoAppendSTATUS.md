# TSO append preservation

TsoAppendDefs and TsoAppendProofs implement the untouched-address frame laws from
TsoMemPa.v:1266,1808,2153,2583 and the pure timestamp-map update in
TsoCtx.v:3951–4050 at the paper pin.

`append_touch_lookup` excludes only the newly appended message when it misses
the selected byte. `ownLastFloor_append_frame`, `windowOK_append_frame`,
`releaseOK_append_frame`, and `wordPinOK_append_frame` preserve all original
floors, word predicates, history functions, ownership bounds and visibility
obligations. `timestampOK_append_frame` retains every payload arm and requires
only actual pointwise memory equality at the untouched byte.

`appendTimestamps` replaces all written entries with `(oldLength+1,payNone)`.
Its right-hand replacement operand accounts for Std.ExtTreeMap's right-biased
union. `timestampMapOK_store` proves the complete updated map interpretation
for the actual authored message and functional memory overlay, including all
framed payloads. `timestampDomain_store` proves the matching domain equation.
These are pure preservation laws, not a native store WP or resource update.

Validation: the 334-job component build passes. A fresh physical-origin audit
checks all 21 logical declarations and their statement/proof dependencies using
only propext, Classical.choice and Quot.sound; no unsafe/partial dependencies or
runtime companion exclusions. Records: `/tmp/xv6-lean-research/TsoAppendAudit.lean`
and `tso-append-audit.log`. Independent review passed; see docs/reviews/tso-append-review.md. The native
TsoStore consumer is a separate work item.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
