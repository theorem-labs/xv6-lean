# Actual active-hart dispatch and mycpu preparation

Implemented and owner-frozen for independent review. Five modules:
`MycpuActive{Defs,Spec,Plan,Proofs,Link}.lean`. Source pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`factor` is an unconditional kernel equality for actual `run_hart_active stepNo`:
read current privilege, perform actual interrupt dispatch, return the pending
interrupt result or perform actual fetch and the complete `afterFetch`
continuation. `afterFetch` retains all fetch/extension errors, printing branch,
landing-pad traps, compressed-extension-disabled result, decoding and execution
outcomes. `stepNo` is arbitrary. No alternate interpreter or execution oracle
is introduced.

`dispatch_plan` includes the initial current-privilege read and reuses the
existing native partial-register interrupt plan. The actual mip and both
external-pin reads remain independent universal branches, without extra owned
cells. The source delegation, misa.S and disabled-SIE premises remain explicit.

`decode_plan` reuses all fourteen exact actual decoder certificates. A local
proved transfer of the existing `snapshotPlanRun` certifier into
`RegisterPlan.Returns` checks membership for each populated snapshot register.
Its RAM oracle is identically absent; memory, writes and missing snapshots
cannot pass. No new evaluator or full-register ownership is required. The
existing decoder premises are unchanged: full source misa for compressed rows;
Supervisor and source menvcfg value for the two base rows.

`prepare_prefix` proves the actual continuation at the indexed fetch result
reaches `executeTail i`, after real decoding, landing-pad validation, a second
Zca query on compressed rows, a PC read, and the actual nextPC write.
The one fourteen-cell footprint is the existing fetch nine plus mie, mideleg,
menvcfg, elp and full nextPC. All read shares are explicit; the repeated cells
are reused sequentially. Uniqueness and length are proved.

The prepared register file writes only nextPC. Its value is PC plus the actual
instruction size `MycpuDecode.width i`, with modular 64-bit arithmetic; it does
not use the fetched window size. Thus a compressed instruction fetched in an
aligned four-byte window advances by two. `prepared_nextPC`, `prepared_other`
and `prepared_pc` expose the exact projections.

Landing-pad validation has its own `elp = 0#1` premise and owned elp cell. The
actual query reads elp directly; menvcfg.LPE=false is not used as a substitute.
The post-fetch prefix requires actual `MycpuFetch.Config`, the exact checked
decoder configuration and landing fact. It does not claim cold boot has already
entered this supervisor Bare configuration.

`executeTail` implements exactly one ExecuteAs redirection and wraps the returned
result verbatim as `Step_Execute` with the actual zero-extended instruction bits.
`compressed_tail` uses the checked compressed expansion to expose the normalized
body directly. `base_tail` exposes the normalized first execute while retaining
its actual ExecuteAs match. No assumption that arbitrary execution cannot return
ExecuteAs is inserted, and a second ExecuteAs is not recursively followed.

`Prefix` is a structural proof of actual register-only progress to an actual
residual body. `Prefix.fold` is the ordinary native bind rule from the residual
body's WP; it is not a closed active-step correctness theorem. The separate
`Spec` and `actualSpec` link discharge the actual factoring, dispatch and
preparation contracts without any body-execution hypothesis. Public
`plan_weaken` and `Prefix.weaken` support a larger unique shared footprint
without duplicating overlapping register ownership.

Source mapping:

| Source/model | Checked correspondence |
| --- | --- |
| Generated `Step.lean:321–396` | Full active-hart factorization, exact post-fetch branches, preparation and one-redirection wrapper |
| `ZicfilpRegs.lean:253–255` | One actual elp read and explicit false landing-pad premise |
| `DecodeExt.lean:204–209`, existing `MycpuDecode` certificates | Actual compressed/base decoder events and unchanged exact configuration |
| `SmodeCore.v:173–245` | Dispatch/fetch/decode/preparation structure; actual body correctness is still a separate obligation |
| Existing `SupervisorInterrupt` | Three universal mip/pin reads and exact four-cell source suppression proof |

Scalar, memory and return-body composition, retirement, full instruction-cycle
WP, KPT translation, complete source `instr` assertions, mycpu function WP and
whole-kernel safety remain separate. The boundary preserves the post-fetch
register file rather than asserting arbitrary translation has no state effects.

Validation:

- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.MycpuActiveLink`
  passed 575 jobs. Plan 3.5s, Proofs 1.0s, Link 851ms; final files have no warnings.
- Fresh physical-origin audit passed all **123 declarations** in the five
  modules, including private helpers, matcher helpers and constructors. Full
  type/opaque-value/constructor dependency traversal and `collectAxioms` on every
  declaration: zero excluded roots, no unsafe/partial logical dependency, only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Evidence: `/tmp/xv6-lean-research/MycpuActiveAudit.lean` and
  `/tmp/xv6-lean-research/mycpu-active-{build,audit}.log`.
- Ordinary kernel proofs establish free-monad/ExceptT reassociation and matcher
  equivalence; no assumed `LawfulMonad SailM` instance or new axioms are used.
- No `sorry`, native decision procedure, generated semantics edit, camera slot,
  allocation, frozen dependency edit, or umbrella change.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
