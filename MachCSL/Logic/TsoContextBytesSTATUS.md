# Physical context byte windows

The four TsoContextBytes modules are implemented and frozen for review.
`window` is exactly the separating conjunction of the existing context-owned
physical bytes over `List.range n`, with actual modular `addressAdd` and
`nthByte` of a `BitVec (8*n)`. There is no alignment assertion or fixed-width
padding. Generic laws cover arbitrary n, including zero; no width bound or
nonwrapping hypothesis is imposed on read aggregation.

`load_fact` and `load` instantiate the actual byte-level TsoContext.load_fact
at every byte and the same arbitrary allowed view. They derive both ReadsBytes
and actual readBytes equality, preserving the complete heap/metadata, TSO,
context and window. Timestamp authority and the actual clean-floor/authored-
dirty alternative justify visibility; no image immutability or all-view
readability assumption is supplied. `agree` derives word equality from actual
byte fragments without needing an authority premise.

Ownership helpers retain the exact fraction semantics. `byte_split` and
`window_split` split both byte and timestamp fractions together and reuse only
the persistent visibility evidence. `byte_persist`/`window_persist` perform
native updates of both fragments to discarded ownership; they do not leave
behind a mutable fragment. The discarded instances are persistent.
`zero_byte` requires matching fractions at timestamp zero;
`of_stored_zero` consumes existing full stored-window clients.
`of_pristine_discard` consumes discarded bytes plus genuinely discarded
pristine timestamps. It never infers a requested owned timestamp fraction from
a discarded receipt. No new authority or runtime name is allocated.

`slice_acc` retains a linear reassembly wand for the exact selected sublist.
`slice_eq_window` reindexes it at `addressAdd a lo` from the precise word-byte
identity and `lo+len≤n`; `subwindow_acc` exposes that actual smaller window
and its restoration wand. Address arithmetic remains modular. This allows
sequential overlapping fetch windows without duplicating owned clients.
Concrete mycpu initial allocation remains separate: its fourteen overlapping
fetch windows must be extracted from the unique 34-byte span once or obtained
from legitimate persistent code ownership.

Source pin: xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. This is a
physical byte aggregation of the existing TsoCtx.v context byte and load
contracts (`TsoContextDefs/Proofs`), rather than the source's aligned eight-byte
virtual `ctx_word` assertion. RiscvPtsto.v:1515–1522 `text_pointsto` additionally
contains KP_rx mapping, canonicality, text-address and tier pins. No such
virtual/text resource is claimed here. Its discarded physical byte/pristine
components motivate the explicit clean-discard bridge, but the full source
text and KPT/walker ownership bridges remain open.

Validation: the combined generic window/event target
`tools/lake.py build MachCSL.Logic.TsoContextBytesReadWPLink` passed 481 jobs;
window proofs approximately 1.1 s. The fresh eight-module physical-origin audit
is `/tmp/xv6-lean-research/TsoContextBytesAudit.lean`, with output in
`tso-context-bytes-audit.log`; it checks all physical declarations, types,
opaque theorem bodies and inductive constructors. All 53 logical declarations
passed with only propext, Classical.choice and Quot.sound, zero exclusions and
no unsafe/partial semantic dependency. No model or prior-owner
file was changed, and no camera slot, axiom, sorry or native decision tactic
was introduced.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
