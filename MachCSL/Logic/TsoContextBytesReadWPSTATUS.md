# Native arbitrary-width context byte reads

TsoContextBytesReadWP{Defs,Spec,Proofs,Link} is implemented and frozen for
review. It reuses the same actual context capacity/name conversions as
TsoContextReadWP, while the owned window has arbitrary Nat width and no
alignment requirement. The request's dependent index is exactly that width;
all its other metadata remains intact. No new camera, name or state
interpretation is introduced.

`power_word_read` opens/restores the complete live era, including heap metadata,
and derives all-view readability from TsoContextBytes.load_fact.
`wp_read` constructs the existing MemoryReadWP plain-read callback internally:
it requires only generation certificate, running context and actual fractional
window, with deviceAddress=false and accessExclusive=false. The guarded
continuation receives the same context/window plus the actual chosen-view
receipt and resumes with the real `.Ok (word,none)` result. It assumes no
readability or successor-preservation oracle, empty log or top view.

The actual generic MemoryReadWP rule pays view advancement and restores the
fixed observation/state interpretation. Existing dead-generation rules handle
power changes. `step_inv` is a separate pure inversion helper conditional on
its stated readability fact; that condition is derived internally for the
native rule, not exposed as a native-rule premise. `advance_frame` states the
unchanged memory/log/register/reservation fields. `wp_read_reservation` frames
and returns the same optional reservation; no exclusive snapshot is created
or cleared. `wp_read_normal` and `wp_read_builtin` retain the exact V1 request.
`nativeSpec` supplies the public contract from these proofs without subordinate
implementation assumptions.

This lifts the source HartEvents plain RAM-read contract through the native
registered-context byte payer. It generalizes the earlier eight-byte adapter,
leaving that module unchanged. Generic zero-width/all-Nat behavior follows the
actual event semantics. Physical PMA/PMP alignment restrictions, checked fetch
widths two/four, actual virtual fetch and source text allocation are separate
layers; this module does not claim arbitrary physical accesses pass PMA.

Validation: `tools/lake.py build MachCSL.Logic.TsoContextBytesReadWPLink` passed
481 jobs. The new native proofs/link each compile in about one second.
`/tmp/xv6-lean-research/TsoContextBytesAudit.lean` checks the complete eight-module
window/event slice, including private/generated declarations and full type,
opaque-body and constructor cones; evidence is `tso-context-bytes-audit.log`.
All 53 logical declarations passed with only propext, Classical.choice and
Quot.sound, zero exclusions and no unsafe/partial semantic dependencies. No generated
semantics change, new axiom, sorry, unsafe/partial implementation or native
decision tactic was used.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
