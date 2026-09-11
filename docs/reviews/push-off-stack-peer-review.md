# push_off stack bodies: independent review

PASS for the frozen fifteen-module PushOffStack boundary. The reviewing
agent read all implementation bodies, the twenty public contracts, design
and STATUS independently of their implementation by the lean_logic_audit
agent. No production edits or signature changes were needed.

The reviewed manifest is the fifteen PushOffStack modules listed in
`Xv6/Kernel/PushOffStackSTATUS.md`, from AuxDefs through WordProofs. All
fifteen implementation SHA256 values and five source/generated-input
SHA256 values still match the owner's frozen manifests under
`/tmp/xv6-lean-research/push-off-stack-{freeze,source}.sha256`.

Source correspondence was checked against xv6iris arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`: CodePushOff.v's three
C.SDSP and three C.LDSP expansions; ProofPushOff.v's save sequence around
lines 630–690 and restore/frame reconstruction around lines 400–480;
StackOwn.v's modular address, region split and four-word laws. The actual
generated execute_LOAD/execute_STORE and vmem_read/vmem_write definitions
were also inspected.

The six normalized instruction indices are exactly 1/2/3 and 14/15/16:
RA/x1, S0/x8 and S1/x9 at current SP+24/+16/+8. The instruction factors
retain the store source-register read before SP, the load SP read and
destination write, effective-address transformation and all underlying
memory effects. Width is eight bytes throughout. Generated STORE's raw
successful-false response still returns Retire_Success, and original
error responses survive both factors. Native ownership, rather than a
caller success assertion, supplies the successful memory result.

The native rules borrow seven owned common cells and frame the other 43.
The KPT branch retains the separate actual shared residue, the complete
hit/miss and A/D guard structure, facts inside the observed branch, actual
reservation and translation receipts, followed by the data-event guard.
The Bare branch opens the actual existential SATP/PMP ownership, patches
only these three keys and uses ten cells plus the same 43-cell frame.
Mode, TOR, alignment and RAM geometry are derived from these resources
and the original identity-tier word. It restores that same slot and the
original-tier word using an internally proved, value-polymorphic closing
wand. Loads keep the incoming Bare reservation; stores return none.

Both branches restore the full source packet, native running-context
ownership, selected-view receipt and literal caller frame. A load changes
only its selected nonzero GPR, preserving SP and every stack address.
The reversible four-word resource equivalence keeps the three saved
words plus the untouched gap at entrySP−32, with arbitrary original
contents and original tier/context ownership. Its arithmetic is modular;
no global no-wrap premise or context reindexing was introduced.

Independent validation passed:

- Fresh `tools/lake.py build Xv6.Kernel.PushOffStackLink`: 1,121 jobs.
- Fresh strict audit: all 284 physical-origin declarations in all fifteen
  modules, including private names (`setExporting false`), every type,
  opaque body and inductive constructor. The traversal explicitly checks
  dependency axioms and rejects missing dependencies, unsafe/partial
  dependencies and designated initial snapshot allocators. Only
  propext, Classical.choice and Quot.sound occur; zero exclusions.
- All 24 owner's kernel checks replayed: six generated-body equations,
  three ordered store factors, modular fixed-anchor and wrapping cases,
  destination/SP preservation, false/error responses, reservation cases
  and footprint size.
- Seven additional reviewer kernel checks passed with an enforced axiom
  allowlist. Actual generated loads into RA/S0/S1 each recover the full
  `0x80000000ffffffff` word while preserving SP. Actual generated store
  prefixes reach eight-byte requests at `0x80040018`, `0x80040010` and
  `0x80040008`, with three distinct full-width source values and unchanged
  SP. An empty-memory load is rejected. Store-prefix checks stop at the
  real write event; they are not claimed as separate complete-machine
  store executions.

Evidence is retained in `/tmp/xv6-lean-research/`:
`PushOffStackPeerAudit.lean`, `PushOffStackPeerChecks.lean`,
`push-off-stack-peer-build.log`, `push-off-stack-peer-audit.log`,
`push-off-stack-peer-checks.log` and
`push-off-stack-peer-execution-checks.log`.

The boundary remains a normalized-body rule over the disabled-SIE common
packet. Its common Config includes the documented sufficient ADUE1 fact
also in Bare mode; it does not invent a Bare ADUE read. Fetch/decode,
enabled-SIE prologue/migration, cycle/function composition, whole source
capability restoration and source entry inhabitation remain separate
obligations. This review does not extend any Fable review's scope.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
