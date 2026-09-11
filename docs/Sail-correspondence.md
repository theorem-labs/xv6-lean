# Sail V1 correspondence: source audit and checked result slice

This is a correspondence design against the paper's `arxiv-v1` artifact, not a
proof that generated Lean RISC-V implements its Rocq machine. The checked slice
in [Correspondence.lean](../MachCSL/Sail/Correspondence.lean) transports common
**result carriers** and continuation predicates. Requests, programs, state,
restarts, blocked accesses and whole-machine simulation remain obligations.

## Exact sources

- Paper artifact: [`mit-pdos/xv6iris` at
  `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`](https://github.com/mit-pdos/xv6iris/tree/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476),
  tag `arxiv-v1`. Its [README](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/README.md)
  specifies Rocq 9.0.1 and coq-sail-stdpp 0.20.1. This audit uses that checkout,
  not the later upstream read/read relaxation or instruction-cache changes.
- Rocq Sail library: [`rems-project/coq-sail` at
  `927111b2f61fe6208a7c24539167a7bec5d9d21d`](https://github.com/rems-project/coq-sail/tree/927111b2f61fe6208a7c24539167a7bec5d9d21d),
  tag `0.20.1`. [V1 outcome and request definitions](https://github.com/rems-project/coq-sail/blob/927111b2f61fe6208a7c24539167a7bec5d9d21d/src-stdpp/ConcurrencyInterface.v#L119-L197),
  [builtin lowering](https://github.com/rems-project/coq-sail/blob/927111b2f61fe6208a7c24539167a7bec5d9d21d/src-stdpp/ConcurrencyInterfaceBuiltins.v),
  and [choice carriers](https://github.com/rems-project/coq-sail/blob/927111b2f61fe6208a7c24539167a7bec5d9d21d/src/Values.v#L905-L934)
  are separate parts of the comparison.
- Sail model: [`zeldovich/sail-riscv` at
  `23dcf8fd923eb8a1958795393d2975632aa940b2`](https://github.com/zeldovich/sail-riscv/tree/23dcf8fd923eb8a1958795393d2975632aa940b2).
- Lean interface inspected: [`theorem-labs/lean-sail` at
  `4cb7fe0eade622c5ce434b4e9ef8f7d0c509ab6f`](https://github.com/theorem-labs/lean-sail/tree/4cb7fe0eade622c5ce434b4e9ef8f7d0c509ab6f),
  [free V1 events](https://github.com/theorem-labs/lean-sail/blob/4cb7fe0eade622c5ce434b4e9ef8f7d0c509ab6f/Sail/ConcurrencyInterfaceV1Free.lean),
  [request records](https://github.com/theorem-labs/lean-sail/blob/4cb7fe0eade622c5ce434b4e9ef8f7d0c509ab6f/Sail/ConcurrencyInterfaceV1.lean),
  and [primitive carriers](https://github.com/theorem-labs/lean-sail/blob/4cb7fe0eade622c5ce434b4e9ef8f7d0c509ab6f/Sail/Common.lean).
  The absence-of-write-payload correction was subsequently source-reviewed and
  published at `28c729b5bb574ae7c32c13353403e57c575d85dd`, now pinned by this project.
  Other comparison obligations below remain open.

## Outcome and local-step table

The source of every machine arm below is
[`RiscvLang.v:mnode_step`, lines 799–945](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/RiscvLang.v#L799-L945).
`tv` is the hart view, `log` the write log, `r` its reservation, and `oth` the
other harts' reserved bytes. Fields not identified as changing are preserved.
A completed event resumes its continuation with the indicated result.

| Rocq outcome / result | Lean event / result | Paper arm and correspondence obligation |
| --- | --- | --- |
| `RegRead reg access_kind` / `reg_type reg` | `readReg reg` / `RegisterType reg` | Read the register file. Translate dependent register types. Rocq carries `option sys_reg_id`; Lean omits it. Paper ignores it, but exact event-label equality requires a projection or a reachability theorem establishing `None`. |
| `RegWrite reg access_kind value` / `unit` | `writeReg reg value` / `Unit` | Update only that register. Same metadata and dependent-value obligations. |
| `MemRead n req` / `(bv (8*n) * option bool) + abort` | `readMem n req` / `Result (BitVec (8*n) × Option Bool) abort` | Completed read always returns success `(w,None)`. Preserve address, access kind, translation, virtual address and tag through the builtin/request translation described below. |
| `MemRead`, MMIO | same | Partial `dev_read` must return `(w,d')`; update device state only. No response if it returns `None`. Preserve reservation and view. |
| `MemRead`, ordinary RAM | same | For every nonexclusive access, choose `tv ≤ tvn ≤ length log`, with all bytes latest-visible at that same view; advance view to `tvn`. Includes fetch and page-table walk. Do not replace this nondeterminism with one chosen memory value. |
| `MemRead`, exclusive RAM, overlap | pending `readMem` | Keep the pending computation; release this hart's reservation. No response is consumed. Requires a separate blocking rule, not a completed free-event step. |
| `MemRead`, exclusive RAM, disjoint | completed `readMem` | Read flat memory, set view to log top, reserve the returned byte snapshot. Preserve byte-width and footprint equalities. |
| `MemWrite n req` / `option bool + abort` | `writeMem n req` / `Result (Option Bool) abort` | Completed write returns success `None`. Rocq outcome request has a mandatory value; Lean request retains an optional value. See the significant builtin mismatch below. |
| `MemWrite`, MMIO | same | Partial `dev_write` updates device state and clears reservation. No log/view change. |
| `MemWrite`, RAM, overlap | pending `writeMem` | Keep computation and all local state, including reservation. Requires a separate blocked rule. |
| `MemWrite`, RAM, disjoint | completed `writeMem` | Update flat memory and append one snapshot/author message. Clear reservation. Exclusive write advances view past its append; plain store preserves view. |
| `InstrAnnounce opcode:bvn` / `unit` | `instructionAnnounce width opcode` / `Unit` | State no-op. Translate existential width and bits. |
| `BranchAnnounce sz address:mword sz` / `unit` | `branchAnnounce width address` / `Unit` | State no-op. Rocq width is an integer; justify conversion to natural width. |
| `Barrier b` / `unit` | `barrier b` / `Unit` | Set view to `fence_post h log (fence_drains b) tv`. Translate barrier constructors; do not discard the fence effect. |
| `CacheOp op` / `unit` | `cacheOp op` / `Unit` | State no-op; preserve payload under architecture mapping. |
| `TlbOp op` / `unit` | `tlbi op` / `Unit` | State no-op; preserve payload. |
| `TakeException fault` / `unit` | `takeException fault` / `Unit` | State no-op at this node; architectural exception actions occur in Sail code. |
| `ReturnException pa` / `unit` | `returnException pa` / `Unit` | State no-op; preserve address. |
| `TranslationStart ts` / `unit` | `translationStart ts` / `Unit` | State no-op; preserve payload. |
| `TranslationEnd te` / `unit` | `translationEnd te` / `Unit` | State no-op; preserve payload. |
| `CycleCount` / `unit` | `cycleCount` / `Unit` | State no-op. |
| `GetCycleCount` / `Z` | `getCycleCount` / `Nat` | Paper returns exactly integer zero. Natural zero can correspond, but carrier mismatch and continuation conversion remain unproved. |
| `Message text` / `unit` | `print text` / `Unit` | State no-op; preserve message content if labels are observed. |
| `Choose ty` / `choose_type ty` | `choose primitive` / `primitive.reflect` | Paper permits every member of the source carrier. See choice table below. |
| `GenericFail message` / `False` | `error error` / `Empty` | Paper has no step. Translate failure tags/messages and catches; equal impossibility of a response alone is insufficient. |
| `Discard` / `False` | `discard` / `Empty` | Paper has no step. Lean generic execution also cannot resume this event. |
| `ExtraOutcome extra` / arbitrary indexed carrier | user exception represented through `error (.User e)` and catching machinery | Paper's final fallback has no step, regardless of the extra carrier. Prove matching catch/early-return lowering before claiming correspondence; no general event mapping is supplied. |
| `Ret ()` (not an outcome) | `FreeM.pure ()` | Paper restarts `riscv_step tick` for nondeterministically chosen Boolean `tick`, and clears reservation. Generic `Execution.Step` has no pure-node transition, so the machine must add this outer rule. |

The four draining barriers are `rw_rw`, `rw_r`, `w_rw`, and `w_r`; other barriers,
including `fence.tso` and `fence.i`, do not drain in this pinned paper model.
See [`fence_drains`](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/RiscvLang.v#L735-L746).
The stateful blocked rules above are not unconditional stuttering. In particular,
blocked exclusive reads can change the reservation without consuming a result.

## Choice and builtin gaps

| Rocq choice | Actual source carrier | Lean choice carrier | Status |
| --- | --- | --- | --- |
| `ChooseBool` | `bool` | `.bool`: `Bool` | Common carrier after base-type translation. |
| `ChooseInt` | `Z` | `.int`: `Int` | Common carrier after integer translation. |
| `ChooseString` | `string` | `.string`: `String` | Requires source string/character encoding relation. |
| `ChooseBitvector n` | `mword n`, integer width | `.bitvector n`: `BitVec n`, natural width; `.bit`: `BitVec 1` | Width conversion and bitvector representation proof pending. |
| `ChooseNat` | **`Z`, including negative integers** | `.nat`: `Nat` | Not the same choice set. No correspondence supplied. |
| `ChooseRange lo hi` | **all `Z` in `mnode_step`** | `.fin n`: `Fin (n+1)` with an offset in `undefined_range` | Not the same choice set. No correspondence supplied. |
| `ChooseReal` | Rocq `R` | No primitive | Missing mapping or proved unreachable case required. |

`choose_prop` is not a premise of the paper's `Choose` arm. In the pinned Sail
library it is even `True` for `ChooseNat`. Restricting a Lean handler to intended
nonnegative/bounded values would not establish equality of the source choices.
[`choose_from_list` / `internal_pick`](https://github.com/rems-project/coq-sail/blob/927111b2f61fe6208a7c24539167a7bec5d9d21d/src-stdpp/ConcurrencyInterfaceBuiltins.v#L336-L351)
emits an integer range choice and then applies `nth_error` at `Z.to_nat idx`:
negative indices become zero; sufficiently large indices lead to a failure node.
Lean's finite index omits those source choices and failure traces. Any
refinement that permits that difference needs an explicit direction and theorem;
source equality or bidirectional trace preservation must not be assumed.

The [Rocq memory builtins](https://github.com/rems-project/coq-sail/blob/927111b2f61fe6208a7c24539167a7bec5d9d21d/src-stdpp/ConcurrencyInterfaceBuiltins.v#L384-L447)
perform an additional lowering layer. Requests entering these builtins have
integer widths, a `size` field, and optional write values. The emitted outcome
uses `Z.to_N n`, drops `size`, casts bitvectors/virtual addresses, and unwraps a
present write value. In particular, **a write with value `None` returns pure
`Ok None` without emitting any outcome**. The initial Lean free builtin emitted `writeMem`, even for `None`. The pinned
correction now returns pure `Ok None` in that case; independent source review
and regression tests cover both absent and present payloads. Giving the event no
handler rule would instead have made it stuck and would not match the source. Extra retained `size`
metadata also requires a label projection; equality with the source outcome
cannot simply compare all request fields.

There is also a program-lowering distinction for announcements: the pinned
[generated `rv64d.v`, lines 6799–6803](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/model-xv6iris/rv64d.v#L6799-L6803)
defines instruction and branch announcements as pure unit functions. Although
the abstract outcome type and `mnode_step` contain announce arms, these generated
wrappers do not emit them. The generic Lean free wrappers do emit events, but the actual stock-generated
`Common0.lean` defines separate pure wrappers, matching these Rocq definitions.
The prototype currently uses those generated pure wrappers. Preserve that lowering
when integrating the model; switching to the generic event-emitting wrappers
would add steps and would need an explicit correspondence argument.

## What the Lean proofs establish

`ResultCode` packages a total encoder/decoder with both inverse laws. `sumCode`
transcribes source success/abort sums as Lean Sail `Result`, preserving both
branches. Specialized codes typecheck against actual `Event.Result` for register
reads/writes, memory read/write responses, barriers, messages, and Boolean,
integer, string and natural-width bitvector choices. `exists_encoded_iff`
preserves existential result predicates, and `continuation_iff` transports
pointwise continuation equality in both directions. The success-response lemmas
match the paper's completed memory arms. These are checked Lean algebraic facts;
the source carrier interpretation remains a manual transcription.

There is no fabricated total mapping for natural/range choices, optional-write
requests, cycle counts, extra outcomes, or arbitrary integer widths. No source
Rocq definition has been imported into Lean's kernel. No event handler for the
paper's state has been proved, and no generated instruction correspondence or
MachCSL adequacy follows from these lemmas.

Next, establish base/register/architecture encodings and reproduce the source
builtin lowering. Then state a relation on computation nodes and complete
machine states with explicit completed-event, blocked-access and restart rules.
Prove each table arm against that relation, quantify over all admitted responses,
and lift through bind/catch and the instruction cycle. The existing generic
`Execution.Step`/`Steps` laws can support completed-event composition; they do
not supply the machine rules or resolve the listed representation gaps.

Validation: `lake build MachCSL.Sail.Correspondence` on Lean 4.32.2. The inverse
laws, memory success lemmas and predicate/continuation
transport proofs use no axioms. No `sorry`, custom axiom or native proof
shortcut is introduced.

## Observed generated Boolean event differences

Native supervisor proofs exposed additional existing program-lowering
differences at the pinned sources. Rocq's getPendingSet uses short-circuit
monadic Boolean helpers and skips the MIE status read under Supervisor;
the generated Lean expression eagerly emits both mstatus reads. Likewise,
Rocq should_inc_mcycle/should_inc_minstret skips its configuration read when
CY/IR is inhibited, while generated Lean emits mcyclecfg/minstretcfg before
applying Boolean conjunction. Exact sources and read sequences are recorded
in SupervisorInterruptSTATUS.md and SupervisorClockSTATUS.md.

The Lean proofs retain these actual events and handle every required branch.
They do not erase ignored reads or infer exact event-tree equality from the
identical returned value. A simulation accounting for such extra read events,
or a separately reviewed generator correction with regenerated proofs, is
still required by the whole-model correspondence obligation. The completed
Rocq replay and printed assumption reports do not discharge it.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
