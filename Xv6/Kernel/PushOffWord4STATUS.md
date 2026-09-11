# PushOffWord4 normalized bodies

Complete and frozen: all 23 approved contracts are implemented. Sixteen
modules comprise seven PushOffWord4Bare modules (Defs, Spec, Pure,
ReadPlan, WritePlan, Proofs, Link) and nine body modules (Defs, Spec, Pure,
Factor, Resources, Rules, MemoryProofs, Proofs, Link). No approved public
contract was changed during implementation.

The actual normalized source rows 8/11 load signed noff32 from a0+120 into
a5; rows 13/22 store low32(a5) at a0+120/124. The source's misleading
second-load zext comment is not executable behavior: the source AST,
register-update formula and actual generated load all sign extend.
The common 50 packet, same original-tier word, running context,
reservation and arbitrary frame are preserved, except the actual load
updates a5 and store updates the word. All control registers, a0 and SP
remain unchanged. A separate pure law relates each compressed execution
to its actual ExecuteAs normalized instruction.

KPT uses the closed KptMemory4 rule with seven borrowed register cells and
43 remaining cells, keeping the separately folded actual four-register
residue. All hit/miss/A-D guards, branch-local CompletedFacts,
translation receipts and reservation evolution remain, followed by one
ordinary data-event guard/view. Bare opens the supplied existential SATP
and PMP cells, borrows ten of the resulting 53 keys and returns the 43-key
remainder and exact source bit/x0 resources. It derives a physical window
and alignment/RAM geometry from the original identity-tier Word4 resource,
then closes the actual stored bytes using its funded value-polymorphic
wand. Bare has one data-event guard/view, unchanged load reservation and
cleared store reservation. KPT keeps either admitted original tier;
identity-only Bare compatibility is explicit.

The previously missing Bare size-four transform/vmem composition is now
implemented by actual finite plans and native read/write rules. It reuses
actual SupervisorRead4/Write4, Outer4, EA4 and Bare translation, with no
new model/camera and no caller physical-value or successful-response
oracle. All raw read/error and write/false tails remain in those actual
programs. The final native body wrapper internally discharges both
memory routes and the actual destination write; no component WP is input.

Validation:

- Link GREEN: 1,186 build jobs, no warnings. Final MemoryProofs and body
  Proofs compile in approximately 1–2 seconds each.
- Strict owner audit: 366 physical declarations in 16 modules, including
  private/generated declarations; full type, opaque-body (`allowOpaque :=
  true`) and datatype-constructor dependency traversal; standard
  propext/Classical.choice/Quot.sound only; no unsafe/partial/Initial
  dependency; zero exclusions.
- Eighteen kernel boundary-check theorems with enforced axiom allowlist.
  Actual generated loads check 0, maximum positive, minimum negative and
  all-ones signed32 results, plus the repeated second load. Actual store
  prefixes reach the exact real four-byte write requests at 120/124 with
  low32 payload and unchanged a0/a5. These are pauses before the real
  write, not fabricated write transitions. Other checks cover missing
  RAM rejection, four-but-not-eight alignment, page/RAM ends,
  misalignment, both instruction Boolean tails, errors, source row indices,
  payload metadata and Bare reservation outcomes.

Evidence under `/tmp/xv6-lean-research/`: `push-off-word4-native-build.log`,
`PushOffWord4OwnerAudit.lean`, `push-off-word4-owner-audit.log`,
`PushOffWord4Checks.lean`, `push-off-word4-checks.log`, and exact freeze
manifest `push-off-word4-freeze.json`.

This is the normalized body boundary. Fetch, decoder WP, source-cycle
composition, noff arithmetic bounds, intena semantic invariant and the
full push_off/function theorem remain subsequent work. No frozen neighbor
or umbrella was edited.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
