# PushOffWord4 independent implementation review

PASS. OpenAI Codex agent `lean_logic_audit` independently reviewed the
implementation by agent `sail_audit`. This review covers all sixteen frozen
Lean modules, their native Links, STATUS and design; it is a complete
implementation review, separate from the coordinator's earlier approval of
the 23 interface contracts. No implementation changes were made or requested.

The manifest is the seven `PushOffWord4Bare` modules (Defs, Spec, Pure,
ReadPlan, WritePlan, Proofs, Link) and nine `PushOffWord4` body modules
(Defs, Spec, Pure, Factor, Resources, Rules, MemoryProofs, Proofs, Link).
All were read in full. I also read the full pinned `CodePushOff.v`, the
relevant `ProofPushOff.v:274–410,740–778,852–878` and
`WpSconfMem.v:2781–2808,3402–3435` contracts/proofs, and the actual generated
`InstsEnd.execute_LOAD`/`execute_STORE` and `VmemUtils` virtual-memory
paths. The source pin is `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

## Source and native behavior

The actual normalized rows 8 and 11 read a0+120 and sign-extend the returned
32-bit word into a5. Rows 13 and 22 store low32(a5) at a0+120 and a0+124.
The second-load source comment saying zext is inconsistent with its AST and
register-update formula; the implementation correctly follows the executable
signed LOAD. The factor proofs retain source-before-base register reads for
stores, the actual address-extension/transform calls, the LOAD destination
write, both STORE Boolean tails, and raw error results. Compressed expansion
is a separate exact program equality; there is no decoder or fetch premise
hidden in the normalized-body contract.

The Bare prerequisite composes real transform, translation-mode, translation,
effective privilege, PMA/PMP/MMIO checks and the write-EA stage. The finite
OneRead/OneWrite judgments expose a real memory event and preserve its raw
response residuals. Native context rules pay that event and its blocked
behavior internally. Read views are universally handled; ordinary writes
retain the actual unchanged-view behavior and clear the current reservation.
The public word ownership derives four-alignment, same-page geometry and the
full RAM range. It does not require eight-alignment, a physical word, or a
successful memory response from the caller.

The KPT split borrows seven of the fifty packet cells and retains the other
43, source bit resources and x0 fact. The actual four-register translation
residue stays separately owned and is folded back after native translation.
Bare opens the supplied existential SATP/PMP cells, patches exactly those
three projections, and splits the resulting 53 cells into ten borrowed and
43 framed cells. The proof derives Bare configuration from those owned values;
it does not read the unowned control-file projections as facts. Load
restoration uses the proved full-entry register-file equality, changes only
a5 and preserves the effective addresses, a0, SP, control fields and frame.

Identity word access retains a funded, value-polymorphic closing wand. The
store returns the actual changed physical/context bytes through that wand,
restoring the original virtual word and tier with its mapping resources.
KPT retains the original tier, all hit/miss and A/D branch guards,
branch-local CompletedFacts, translation receipts and actual reservation
evolution before the single data-event guard. Bare admits only identity and
has exactly that data guard, retaining rr for loads and returning none for
stores. Final Links supply the actual native dependencies; the public theorem
has no component WP, memory-success, physical-value or translation oracle.

## Independent validation

- Fresh native Link build passed: **1,186 jobs**.
- Fresh strict audit passed: **366 physical declarations in 16 modules**,
  including private/generated declarations, every type, opaque body and
  inductive constructor. Private lookup explicitly disables exporting;
  unresolved dependencies fail the audit. Root axiom collection and explicit
  dependency-cone axiom checks allow only `propext`, `Classical.choice` and
  `Quot.sound`. No unsafe, partial or Initial-allocation dependency; **zero
  exclusions**.
- All **18 kernel boundary checks** replayed successfully with their axiom
  allowlist. They include actual generated signed-load executions, actual
  store prefixes reaching the four-byte write requests, four-but-not-eight
  alignment, page/RAM endpoints, missing-memory rejection, both Boolean
  instruction tails, errors and reservation outcomes. The store fixtures
  certify the prefix/request boundary, not an invented successful write.
- All sixteen Lean files and both metadata files matched the owner's frozen
  hashes before and after review. Source hashes and observed results are
  recorded independently.

Evidence is under `/tmp/xv6-lean-research/`:
`PushOffWord4PeerAudit.lean`, `push-off-word4-peer-build.log`,
`push-off-word4-peer-audit.log`, `push-off-word4-peer-checks.log`, and
`push-off-word4-peer-results.json`. The replayed fixture source is
`PushOffWord4Checks.lean`.

This establishes the normalized four-byte body boundary with explicit owned
hardware configuration and the existing disabled-SIE packet. It does not
establish enabled-SIE migration, fetched cycles, noff arithmetic bounds,
intena's semantic invariant, full push_off execution, source-entry resource
inhabitation or boot reachability. These limitations match the stated scope.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
