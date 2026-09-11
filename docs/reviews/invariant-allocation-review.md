# Independent review: native invariant allocation

Reviewer: Codex coordinator. Read every Invariant module and the native Iris
`wsat_alloc` and `lc_alloc` implementations. The port uses the same allocations
and validity proofs, with explicit runtime names so the supplied camera-slot
witnesses remain definitionally equal in the resulting instance.

The recursive invariant map, enabled masks, disabled names and credit supply
occupy four distinct slots16–19; all earlier application slots are preserved.
The allocated result contains native world satisfaction, the full enabled mask,
credit authority and matching client credits. Clearing the empty disabled-set
fragment follows the native world allocator exactly. The framing rule preserves
arbitrary existing application ownership.

The machine adapter uses the actual image-parametric language and existing state
interpretation. Its zero extra-later setting retains the mandatory one credit
per operational step; the exact adequacy recurrence is proved to equal the step
count. No machine WP, initialized application invariant or adequacy theorem is
assumed by this adapter.

Fresh independent180-declaration axiom audit passed with the three standard
axioms only. Review: PASS for native capacity/allocation and the instance adapter.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
