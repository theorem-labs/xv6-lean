# Native mycpu active-step composition

Frozen five modules: Defs/Spec/Plan/Proofs/Link. `wp_scalar`, `wp_store`,
`wp_load`, and `wp_return` run the actual generated `run_hart_active` with
an ordinary terminal continuation. `actual` and `nativeSpec` discharge all
four public contracts, and `index_complete` checks their fourteen-index
coverage. No final rule has a residual instruction-body correctness or
machine-preservation premise.

All rules use the same unique CycleBody 28-cell footprint, generation
certificate, actual running context, persistent discarded 34-byte boot
span, and reservation custody. The actual indexed fetch window is
extracted through MycpuBootResources without reallocation or fractional
timestamp upgrades. The exact full fetch boundary selects its successful
tail using the owned word; all other V1 responses, errors and possible
second-fetch residuals remain in that boundary. Structural widening
preserves every register event and three universal pending/pin reads.
The unconditional active-step factorization retains interrupt and fetch
failures before the concrete native proof selects its supported branch.

Active.Config is explicit at the original register file: supervisor,
disabled interrupts, Bare translation, TOR grant, PMA/HTIF, actual PC and
width, checked decoder facts, and elp=0. Read/Write/Return body Config is
also stated at the original file. Pure transport lemmas prove that only
nextPC changes during preparation; all those control/address assumptions
therefore still hold. True instruction width determines nextPC even when
the actual fetch reads four bytes for a compressed instruction.

The final register files are exactly scalarAfter/prepared/loadAfter/
returnAfter. The result is Step_Execute(Retire_Success, actual instruction
bits), preserving the single ExecuteAs redirection in the generated body.
Scalar/return consume one memory-event guard and return the fetch receipt.
Loads/stores consume two guards and return both fetch and data receipts,
with no invented ordering relation. Loads preserve the word fraction and
reservation; successful stores replace the full word with the actual
original source-register value and return a cleared reservation. Context,
span and the entire register bundle remain available to the continuation.
The actual source error/store-failure tails are justified by the reused
native memory rules, not removed from the programs.

Source mapping: generated Step.lean:321–396 and Fetch.lean:232–284;
pinned iris/SmodeCore.v:167–248 and all fourteen CodeMycpu.v instructions.
This is a Bare active-step component. Setup, retirement, clock/restart,
function chaining, establishment of supervisor configuration, source KPT
stack/resources, ABI result, and whole-kernel adequacy remain separate.

Validation: final build passed 690 jobs, Plan 1.2s / Proofs 1.5s / Link
865ms. Fresh physical-origin audit passed all 52 declarations in the five
modules, including private helpers, complete opaque bodies, types and
constructor fields. Only propext/Classical.choice/Quot.sound occur; zero
roots excluded and no unsafe/partial logical dependencies. Evidence:
`/tmp/xv6-lean-research/MycpuCycleEntryAudit.lean`,
`mycpu-cycle-entry-{build,audit}.log`, and
`mycpu-cycle-entry-frozen.sha256`. No existing source, generated model,
umbrella or registry was changed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
