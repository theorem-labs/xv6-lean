# Identity/Bare JAL source boundary: native implementation

FROZEN: all 24 reviewed contracts are implemented in 22 Lean modules.
`BareJalSource.nativeSpec` closes the actual source Bare JAL branch with
no caller fetch, configuration, decoder, body-success or retirement WP.
The public continuation is the genuine returned-cycle continuation.

- BareJalFetch (8 modules): generic actual F_Base fetch on nine owned
  cells, identity RX/pristine code, one four-byte or two halfword reads,
  all outer eager register reads, exact guard/view order and full return.
- BareJal (8 modules): reversible 9 + 44 partition of the source fifty
  cells plus actual existential Bare SATP/PMP cells; internally supplied
  fetch, reused KptJal decoder/body plans, active execution and real cycle.
- BareJalSource (6 modules): actual opened identity/Bare input, same-hart
  pmaBoot agreement, native source configuration/certificate extraction,
  whole stack/timer/pending/stvec/hardware/frame preservation and closing.

The JAL writes x1 = original PC + 4 and nextPC = PC + signed immediate;
SP and every other GPR remain unchanged. Code supplies two-alignment,
which combines with target-even to derive immediate encodability. Fetch
at PC mod 4 = 2 reads both halfwords, including offset 4094 across pages.
The second half retains the original fetch start. Native reads leave the
reservation unchanged; actual restart clears it. Both permitted clock
choices and arbitrary next ticks remain quantified by the shell.

All 1,196 build jobs passed without warnings. The owner strict audit
covered all 204 physical declarations, including private declarations,
full types, opaque bodies and datatype constructors: only propext,
Classical.choice and Quot.sound; zero exclusions, unsafe/partial semantic
constants or initial-allocation dependencies. Thirty-one concrete kernel
edge checks passed, including the 53-cell uniqueness/partition, both fetch
alignments, exact split addresses/words/start, negative offsets, odd
immediate rejection and unchanged SP/TP. No giant decoder regeneration
was required; the earlier checked generic KptJal decoder is reused.

Evidence under `/tmp/xv6-lean-research/`: `bare-jal-source-link.log`,
`BareJalOwnerAudit.lean`, `bare-jal-owner-audit.log`, `BareJalChecks.lean`,
`bare-jal-checks.log`, and `bare-jal-freeze.json`. The six original
Defs/Spec modules retained their approved signatures. The independent
interface review is `docs/reviews/bare-jal-source-interface-peer-review.md`;
final implementation peer review is assigned to the coordinator.

Source pin and field-by-field mapping are in
`docs/design/bare-jal-source-boundary.md`. There is no stack-space minimum,
new camera, authority allocation, KPT prerequisite or inference of Bare
from identity tier. The source body requires its actual opened Bare lane
and explicit same-hart boot-PMA ownership. General PMA, source entry
inhabitation/boot reachability and the separate callable dispatcher are
outside this boundary. Frozen neighbors and umbrellas are unchanged.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
