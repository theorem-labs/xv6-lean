# View advancement and pristine read bridges

`TsoReadDefs/Spec/Proofs/Link` port the view-update and pristine-byte bridges
at paper pin `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. Source mappings are
`RiscvExec.v:534–656` (view bound, receipt and monotone advancement),
`RiscvPtsto.v:1505–1513` (`pristine_elem`) and `TsoCtx.v:1887–1970`
(pristine bytes/windows and their all-agent, all-view read consequences).
The full `HartEvents.v` was read to establish the downstream read contract.

`advanceView` changes only the actual selected CPU's view. `writeBack_view`
proves equality to the actual hart-local writeback. Its pure laws preserve
`MemoryOK`, establish the selected value, and show pointwise monotonicity
of the full Nat-agent `avf`, retaining device agents at the log top.
`tso_advance` updates the existing native view authority, frames timestamps,
log entries and length, and mints the exact persistent selected-view receipt.
`era_advance` frames all seven current-era conjuncts. `power_advance` uses
proved fixed-state framing and actual generation-certificate agreement.
The lower bound and log-length upper bound are explicit. No log emptiness,
no chosen schedule, and no successor-preservation oracle is assumed.

`pristineByte` is exactly a discarded timestamp-zero element with the
source empty payload. `pristineWindow` and `byteWindow` are separating
conjunctions over `List.range n` and actual modular `addressAdd` addresses.
`pristineByte_mint` and `pristine_window_mint` turn full initial timestamp
fragments into persistent pristine fragments with the native GhostMap
update. They do not falsely retain writable timestamp ownership.
`pristine_byte_read` combines the complete heap authority with the actual
TSO timestamp authority to recover the timestamp-zero latest byte.
`pristine_window_read` then proves actual `ReadsBytes` at every agent and
every view. Neither operation assumes an empty log or reads current memory
in place of the TSO view. Width zero remains valid; no no-wrap premise is
introduced. `power_pristine_read` and `power_memoryOK` expose these facts
through the actual live fixed-state interpretation.

`TsoReadSpec` separates the public advance/read/mint contracts from their
implementation. `registryTsoReadSpec` discharges them at the existing final
twenty-slot registry. There is no new camera or runtime name.

Validation uses `python3 tools/lake.py build MachCSL.Logic.TsoReadLink` and
`python3 tools/lake.py env lean /tmp/xv6-lean-research/TsoReadAudit.lean`, with
`/data/jason/.elan/bin` on PATH. The audit checks every namespace declaration
and its transitive axioms, permitting only `propext`, `Classical.choice`,
and `Quot.sound`; its log is `/tmp/xv6-lean-research/tso-read-axioms.log`.
No custom axioms, `sorry`, `native_decide` or `bv_decide` are used.

This layer does not yet prove the downstream native memory-read WP,
exclusive/reservation or MMIO rules, or the full context/window load gates.
A current-memory byte cell alone is deliberately insufficient to establish
a plain read at every reachable TSO view.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
