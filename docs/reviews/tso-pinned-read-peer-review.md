# Independent review of context-free pinned reads

Result: PASS for the declared resource-derived per-byte read scope. The artifact-audit Codex agent independently read all five frozen TsoPinnedRead modules, status and supervisor-KPT design, then checked pinned `CtxValues.v:295–300,323–348,375–486`, `TsoCtx.v:5332–5376` and `TsoMemPa.v:2343–2370`. The native timestamp/history/view projections and underlying PinOK definition were also inspected.

`ownAnchor` faithfully records a real byte-writing log message and its Nat author. Its external position is one-based while History.logElem is zero-based. `ownAnchor_valid` uses the actual full history authority and LogRep from tsoInterpAt to establish the exact machine-log lookup and author visibility. Neither lookup nor forwarding is an input assumption. `pin_valid` obtains the exact payload through timestamp authority and TimestampMapOK; the physical byte value need not be the observed byte.

The pure proof differs from the source proof decomposition but establishes the same author-read result. Raising the view to an already-visible anchor only makes older messages newly visible; the descending scan cannot pass that anchor. `readDown_raise_anchor` proves equality of the two actual scans, and PinOK applies at the raised view. The source position-within-log premise is derived from the real logByte lookup. Arbitrary logs, Nat agents and original views remain quantified. No assumption forces the author's current view above the publication bound.

Both source boot-credential arms and all three per-byte anchors are preserved exactly. The implementation uses Views.llb, including its source pure-zero branch, in the boot-hart arm. The credential's log receipt is retained even though the source slot-read proof itself only uses the boot identity there. A secondary hart uses its actual view authority bound. Boot slots separately handle zero floor, an owned authored anchor, or agent-zero's view receipt. The explicit Fin8 CPU-to-Nat-agent conversion is checked in each relevant branch.

The result quantifies every permitted view and every selected modular address, with arbitrary length and fractions. Allowed-set membership is the result: there is no hidden assertion equating an observed PTE leaf to the currently owned physical word. No context token, alignment, no-wrap requirement, readability oracle or current-word assumption was added. `slot_read_preserve` returns the original TSO authority, credential and complete pinned-cell conjunction; native pure extraction and framing preserve these linear resources. Existing byte/timestamp/history/view capacities are reused without a new slot, name, allocation or metadata replacement.

Independent build passed 501 jobs. A fresh physical-origin audit checked all 55 declarations in Defs/Spec/Pure/Proofs/Link, including private helpers, opaque bodies (`allowOpaque := true`), types and constructor fields. Only propext/Classical.choice/Quot.sound occur; zero roots were excluded and no unsafe/partial dependency occurs. Evidence: `/tmp/xv6-lean-research/TsoPinnedReadPeerAudit.lean`, `tso-pinned-read-peer-build.log`, and `tso-pinned-read-peer-audit.log`.

No implementation correction requested. The design's informal pseudocode still calls the boot log receipt `Views.natLB`; the implemented/source assertion is `Views.llb`, as its status correctly states. Canonical PTE assembly, pinned stores, native PTE-event WPs, tree/TLB invariants and actual Sv39 translation remain outside this checkpoint. This review does not assert those later design stages are implemented.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
