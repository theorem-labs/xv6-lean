# Native context-word ordinary read event

`TsoContextReadWP{Defs,Spec,Proofs,Link}` connects the physical context-word
load gate to the actual eight-byte V1 memory event and native Iris WP.
Source references are `TsoCtx.v:2095–2101,4440–4512` (registered physical
bytes and all-view load gate), `ctx_load_ok:1804` for the separate virtual
layer, and the ordinary `HartEvents.v:137–270` read rule already implemented by
`MemoryReadWP`. Source pin:
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The complete relevant physical load gate, existing registered store gate,
ordinary memory-read event implementation, and write callback interfaces
were inspected. This checkpoint implements only the ordinary read WP;
the context-indexed write-event adapter is a separate task.

| Obligation | Implementation |
|---|---|
| Same native context capacity and era names | `contextCapacity`, `contextNames`, link equalities |
| Actual running-context and aligned word resources | `running`, `wordPointsto` |
| Actual selected-view step/result uniqueness | `step_inv` |
| Memory/log/register/reservation identity | `advance_frame` |
| Full native heap/TSO access and restoration | `power_word_read` |
| All permitted views and exact success result | `wp_read` |
| Explicit normal access kind | `wp_read_normal` |
| Actual `sail_mem_read` emission | `wp_read_builtin` |
| Same reservation fragment framed | `wp_read_reservation` |
| Constructed independent native contract | `Spec`, `actual`, `nativeSpec` |

The general event theorem keeps the request explicit and requires
`deviceAddress req.pa = false` and
`accessExclusive req.access_kind = false`. It consumes the actual
persistent generation certificate, running-context ownership, and the
same eight aligned physical byte/timestamp/context cells as
`TsoContextWord.pointsto`. No register bundle, caller-provided readability
predicate, software theorem, or access callback is assumed. The guarded
terminal continuation receives the same context and word plus the actual
selected-view lower-bound receipt, then proves the real residual program
`k (.Ok (word, none))`.

Inside the event callback, `power_word_read` uses `live_era_access` to
open precisely the registered live era and retains its restoration wand.
It reads the complete native heap, including metadata, and the actual
TSO timestamp/log authority. `TsoContextWord.load_fact` proves the same
word readable at every view at least the hart's current view. Clean-floor
and authored-dirty justifications both remain available; this is not a
pristine-only or timestamp-zero approximation. The complete era and
power interpretation are explicitly rebuilt and returned unchanged.
No owned register authority is duplicated or exported to the client.

`wp_read` supplies the existing all-successor ordinary memory rule with
that proved read fact, internally choosing the property `value = word`.
The rule covers every view between the actual CPU view and log length,
proves reducibility, identifies every successful result by byte
extensionality, and performs the actual view-authority update. It restores
full power/era and observation bookkeeping at that successor. The normal
read changes only this CPU's view: memory, log, registers and reservation
are unchanged. The explicit reservation wrapper frames the same fragment;
it invokes neither exclusive snapshot creation nor reservation clearing.
Dead-generation behavior is handled by the existing native read rule.

The result width is **the event index 8**. The request's separate declared
size, virtual address, translation and tag metadata are preserved as
supplied, not rewritten to manufacture a correspondence. The normal-kind
wrapper visibly specializes the general theorem to explicit
`AV_plain`/`AS_normal`; the builtin bridge is definitional and retains its
one actual emitted read event. No model event or generated instruction is
collapsed into an atomic software step.

No new camera or registry slot is introduced. Virtual-address/kernel-tier
mapping, supervisor fetch/translation, a complete load instruction or
`mycpu` WP, and the ordinary context write-event adapter remain separate.
The existing registered store resource theorem is not asserted to be a
write-event WP by this checkpoint.

Validation: the final `TsoContextReadWPLink` target completed **486 jobs**.
A fresh physical-origin audit checked **22 logical declarations in all four
modules**, including opaque theorem bodies and inductive constructors.
Only `propext`, `Classical.choice`, and `Quot.sound` occur; there are no
unsafe or partial logical dependencies and **zero exclusions**. The full
power-resource read bridge, native event WP, builtin/reservation wrappers
and constructed contract were additionally checked with `#print axioms`.
Evidence remains outside the repository at
`/tmp/xv6-lean-research/TsoContextReadWPAudit.lean` and
`/tmp/xv6-lean-research/tso-context-read-wp-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
