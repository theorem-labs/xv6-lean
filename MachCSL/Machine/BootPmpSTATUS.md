# Universal PMP reset facts

`BootPmp{Defs,Program,Proofs}` proves PMP postconditions of the actual
paper boot program for **arbitrary original register files**. The source
loop is generated `PmpControl.lean:356–368`, corresponding to the pinned
Sail `reset_pmp`; boot composition follows the actual `BootProgram`,
`Model.init_model/reset`, `SysControl.reset_sys`, and firmware requirements.

`clearEntry` performs the exact generated A:=OFF then L:=0 updates.
`resetPrefix` records the sequential vector updates, retaining the source's
Int-indexed lookup operation. `prefix_lookup` is a generic loop invariant:
visited entries are reset and all later entries retain their original
values. `clear_mask` identifies the exact mask 0x67; `clear_other` proves
bits 0,1,2,5,6 are preserved.

`loop_run` reasons by induction through the actual generated inclusive
`IntRange.forIn'.loop`, applying the checked register-only evaluator and
Run uniqueness to each four-event body. It proves the final vector is
exactly `resetPrefix 64` and the arbitrary PMP address vector is unchanged.
The full 64-iteration symbolic vector is never reflected as one proof.

`BootPmpProgram` is a proof-only factorization before and after the generated
PMP reset call. `program_eq` checks equality against the **actual** generated
boot chain, using proved free-monad associativity and conditional-bind laws.
Small register-projection proofs show the surrounding programs preserve
both PMP vectors. `run_boot` composes these facts for every completed Run;
it does not modify the executable boot or choose a preferred preboot file.

`bootFacts_off` consequently proves all 64 entries have L=0 and A=OFF for
every CPU in every `BootFacts` state. `off_int` matches the generated Sail
Int lookup exactly; `off_locked` and `off_mode` expose decoded consequences.
No zero PMP-address assumption, zero-other-config-bit assumption, zero
counter assumption, or deterministic boot-state restriction is introduced.

Validation: the final 157-job build passes, with the complete proof module
in 1.1 seconds; `/usr/bin/time` measured 1.95 seconds and 1,704,288 KiB max
RSS for that build invocation. Early coarse transparent vector projections
exceeded a 2M-heartbeat experiment budget; they are excluded from production.
The final implementation uses the structural loop and checked factorization.
The separate enforced namespace/transitive axiom audit passes all 64
declarations, including private proof helpers, and is recorded in
`/tmp/xv6-lean-research/BootPmpAudit.lean` and `boot-pmp-axioms.log`.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed; no custom
axiom, `sorry`, `native_decide`, or `bv_decide` occurs.

`BootPmpPlan` adds the actual generated PMP event plan. The configured
`sys_pmp_count` is **16** and grain is zero, even though reset clears all
64 entries. The plan preserves exactly that 16-entry check loop. It retains
the configuration and address reads performed by `pmpReadAddrReg`, including
the previous-address read for positive indices, and uses A=OFF to prove
`pmpMatchAddr` cannot match independently of both address values. Structural
induction through the actual ExceptT IntRange loop yields `check_off_plan`
for every address, Nat width and access kind in machine privilege. No
configuration/address vector literal, memory fact, permission callback or
existential execution witness replaces those event plans. The complete
register file is unchanged. `bootFacts_check_plan` specializes the plan to
every CPU of every allowed boot.

The plan module builds in 1.0 seconds (393 jobs), and its combined namespace
axiom audit is `/tmp/xv6-lean-research/BootPmpPlanAudit.lean`, with the count
and standard-foundations-only result in `boot-pmp-plan-axioms.log`. These
facts and plans do not prove a complete fetched instruction WP or the
paper's system adequacy.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
