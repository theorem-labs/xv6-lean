# Actual active-hart dispatch and mycpu preparation

Approved bounded contract, now implemented in the five modules below.
See `Xv6/Kernel/MycpuActiveSTATUS.md` for checked results. Read generated
`Step.lean:321–396`, `ZicfilpRegs.lean:253–255`, `DecodeExt.lean:204–209`,
`StepExt.lean:207`, and source `SmodeCore.v:173–245` at pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The next slice factors the actual `run_hart_active`, proves interrupt suppression
and the post-fetch register prefix, and stops at the actual instruction body
with its exact `Step_Execute` wrapper. It does not assume or claim execution
correctness for the body. The coordinator can subsequently compose the separately
proved scalar, memory and return bodies with these boundaries.

## Owned files and factoring

Owned new `Xv6/Kernel/MycpuActive{Defs,Spec,Plan,Proofs,Link}.lean` and
`MycpuActiveSTATUS.md`. No modifications to current owner prefixes, generated
code, or existing decoders/fetch/interrupt rules. No new ghost capacity.

Define `afterFetch stepNo fetched` as the actual four-way fetch-result
continuation from `run_hart_active`, including decoder calls, landing-pad traps,
compressed-extension-disabled result, optional printing, actual execution and
its one redirection. Prove an unconditional kernel equality factoring
`run_hart_active stepNo` as:

```text
readReg cur_privilege >>= fun privilege =>
dispatchInterrupt privilege >>= fun pending =>
  match pending with
  | some (intr, privilege) => pure (Step_Pending_Interrupt (intr, privilege))
  | none => fetch () >>= afterFetch stepNo
```

The equality retains every interrupt, fetch error, extension error and body
outcome. Any necessary reassociation/distribution lemmas are ordinary proofs
about the existing free monad. No alternate interpreter is introduced.

Define:

```text
instbits i = BitVec.ofNat 32 (MycpuDecode.encoding i)
prepared i rs = write rs nextPC
  (BitVec.addInt (rs PC) (MycpuDecode.width i))
executeTail i = do
  let first ← execute (MycpuDecode.decoded i)
  let final ← match first with
    | ExecuteAs other => execute other
    | otherResult => pure otherResult
  pure (Step_Execute (final, instbits i))
```

`MycpuDecode.width` is the instruction size, not the fetched window size.
For example a compressed instruction in a four-byte aligned fetch still
prepares `nextPC = PC + 2`. Prove the exact nextPC projection and preservation
of every other register in `prepared`.

The source performs **one** ExecuteAs redirection, not recursive redirection.
The returned result of the second execute is wrapped verbatim. Prove:

- For compressed rows, the existing checked `compressed_expansion` gives
  `executeTail i = execute (normalized i) >>= Step_Execute_wrapper`.
- For base rows, `base_normalized` changes only the first instruction; retain
  the actual ExecuteAs match on its result, without assuming it cannot occur.

## Fourteen-cell footprint and pure assumptions

Use `MycpuFetch`'s nine cells plus mie, mideleg, menvcfg, elp and full nextPC:

```text
MycpuFetch.footprint shares.fetch ++
[(mie, shares.enable), (mideleg, shares.delegation),
 (menvcfg, shares.environment), (elp, shares.landing), (nextPC, own 1)]
```

This is one unique fourteen-cell footprint. Interrupt shares reuse its existing
misa and mstatus cells. Read-only cells retain arbitrary supplied fractions;
nextPC requires full ownership for its actual write. Neither mip nor external
pin cells are added: the existing interrupt plan branches universally over
those three actual reads.

Pure premises, explicitly separated:

- `MycpuFetch.Config rs i region` for the already proved Bare full fetch.
- `SupervisorInterrupt.Disabled rs`: misa.S, exact machine-interrupt delegation,
  and disabled SIE. This retains arbitrary mip and independent external pins.
- `MycpuDecode.Config i rs`, the actual existing checked decoder assumption:
  source full misa for compressed rows; Supervisor and source
  `menvcfg = 0xa000000000000000` for the two base rows. The existing fetch C-bit
  and interrupt S-bit conditions are not silently generalized away.
- `rs elp = 0#1` for the actual landing-pad query.

`is_landing_pad_expected` reads **elp directly**. Its false result does not
follow from menvcfg.LPE being disabled. Keep that register/resource premise
explicit, matching `SmodeCore`'s landing-pad premise. No full-register reset
snapshot or additional PMP/translation assumption is introduced.

## Concrete register plans and boundary

Prove a `dispatch_plan` on this same footprint for
`readReg cur_privilege >>= dispatchInterrupt`, returning none and unchanged rs.
It widens the existing native partial-register `SupervisorInterrupt.dispatch_plan`
and includes the initial privilege read of `run_hart_active`.

Prove `decode_plan` for all fourteen actual `MycpuDecode.decode i` calls,
returning `decoded i` unchanged, on the fourteen-cell footprint. Reuse the exact
existing decoder certificates. If necessary add a local proof transferring the
already existing `snapshotPlanRun` certificate into `RegisterPlan.Returns`, with
explicit membership for every populated snapshot register and the checked
snapshot coverage. This adds no evaluator and no full 178-register resource.
Only the existing misa/cur_privilege/menvcfg snapshot entries may discharge reads.

Prove `landing_plan` from the actual one elp read and `zca_plan` from its actual
misa read. On the compressed path Zca is checked again after decoding and
landing-pad validation; the earlier fetch check is not reused in a way that
omits this event. The final prefix reads PC and actually writes nextPC.

Use a small structural register-prefix assertion:

```text
Prefix fp rs program body after
| done : Prefix fp rs body body rs
| prefix (first : RegisterPlan.Returns fp rs segment value middle)
         (rest : Prefix fp middle (next value) body after) :
    Prefix fp rs (segment >>= next) body after
```

The principal preparation certificate is:

```text
prepare_prefix shares rs i region stepNo config decodeConfig landing :
  Prefix (footprint shares) rs
    (afterFetch stepNo (MycpuFetch.result i))
    (executeTail i) (prepared i rs)
```

This proves the actual remaining program reaches its actual execute body after
the stated register operations. It has no premise about body correctness and
no predicate named as an execution oracle. `stepNo` remains arbitrary; the
pinned printing flag makes its formatting branch inactive.

The separate `Spec` records factoring, dispatch and preparation contracts.
`Link` discharges them, preserving implementation/spec separation. A generic
native `Prefix.fold` may expose the ordinary rule from a WP of its **actual
residual body** to a WP of the prefix. Such a bind rule is explicitly a partial
composition tool, not a closed active-step theorem. The bounded deliverable
does not claim `WP run_hart_active` by requiring an unknown execution-correctness
hypothesis; full body composition remains coordinator-owned.

## Source scope and validation

Source `exec_hart_active_progress_base_gen` and
`exec_hart_active_progress_RVC_gen` thread the post-fetch state, prepare nextPC,
and consume actual body-execution results. This slice provides the verified
prefix and exact wrapper while preserving the location where those body results
must be proved. It does not substitute cold-boot M-mode for supervisor config,
or assert arbitrary KPT fetch leaves state unchanged.

Compile all five new files, check full physical/type/opaque-value/constructor
cones and standard-three-axiom allowlist. All response and ExecuteAs equalities
must be kernel checked. No native decision procedure, new axioms, generated
semantics edit, camera allocation or source function theorem claim.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
