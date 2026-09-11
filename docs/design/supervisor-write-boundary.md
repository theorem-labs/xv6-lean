# Supervisor eight-byte physical store boundary

Proposal only; implementation awaits agreement. The next bounded result is a
native WP for the actual generated call

```text
checked_mem_write (Physaddr address) 8 new (Store Data)
  PBMT_PMA Supervisor () false false false
```

It consumes real registered-context ownership of the old eight-byte word and
returns the same context with the new word and a cleared own reservation.
It proves the PMA/PMP/MMIO prefix and uses the completed ordinary context-write
WP at the actual memory event. No caller-supplied access proof, state update
callback or whole-store correctness premise is exposed.

Source references are relative to `.upstream/xv6iris/iris`, pinned to
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The actual generated code is
`models/riscv/LeanPaperStock`, from Sail source
`23dcf8fd923eb8a1958795393d2975632aa940b2` and runtime
`28c729b5bb574ae7c32c13353403e57c575d85dd`. This review read the complete
`HartSMem.swp_checked_mem_write_S` proof and surrounding abstract contract,
the relevant context-store/word-store gates, the conditional PTE boundary,
and the actual generated checked-write, write-RAM and physical-check paths.

## Source contract and implementation reuse

`HartSMem.v:2778–2842,2930–3050` stages a supervisor ordinary store using
four register resources: PMA regions, PMP configuration and address vectors,
and HTIF base. Its generic `Wobl`/`Hwrite_node` parameters are discharged by
real context ownership at the source instruction leaves. They are not an
acceptable remaining hypothesis of the proposed native public rule.

`HartEvents.v:299–375` supplies the actual RAM-write node rule. When another
hart's reservation overlaps, it retries the same event with the same state
and incoming reservation. Otherwise it appends the writer's message, updates
the bytes, clears its own reservation, and resumes with `.Ok none`. Ordinary
stores keep their existing CPU view. `TsoCtx.v:2572–2592,4346–4371` supplies
the registered-context finite-map/window update with full heap and TSO
resources. `SmodeCorePt.v:573–634,708–737` adds the virtual word/tier mapping
bridge; that bridge is outside this physical-address checkpoint.

The frozen native `TsoContextWriteWP.wp_write_normal` already discharges the
entire physical/context update, including full native heap metadata, timestamp
and dirty-set updates, authored log append, reservation update, observation
bookkeeping and blocked retry. Its `write_effect` and `step_inv` identify the
actual state changes. The new wrapper must use this implementation directly,
not reconstruct or assume its resource obligation.

The new prefix reuses:

- `Machine.SupervisorPhysical.RamRange`, `clint_ram`, `sig_ram`, and
  `device_ram` for the actual RAM interval and device guard.
- `Logic.SupervisorPmp.check_ram_plan` specialized to `Supported.store`,
  for the actual first TOR entry and its W grant. The existing source-shaped
  `TorRam` package also contains R/X permissions; that is the canonical
  source configuration, not a claim that ordinary stores inspect R/X.
- `RegisterFootprint` and `RegisterPlan` for the four separately supplied
  fractions and unchanged register-file prefixes.
- `TsoContextWord.aligned` and its checked generated-alignment bridge to
  obtain eight-byte alignment from the owned word itself.

`SupervisorPhysical.SupportedRead` and `ReadGrant` deliberately do not cover
stores. Add store-specific PMA and writable-MMIO lemmas in the new owned
prefix; do not pass a store through a read grant or modify those frozen files.

## Actual generated path

`Mem.lean:534–582` performs the following sequence for this exact API:

1. `check_pma_with_pmp_priority` reads `pma_regions`, finds the stated actual
   matching region, checks its PBMT_PMA-overridden `writable` field, and
   checks alignment through `mag_pma_check`. The Data-store assertion checks
   the explicit false conditional flag. The result is `Ok (CannotSplit,0)`.
   This successful priority branch performs no PMP read.
2. `split_misaligned` returns `(1,8)` because splitting is forbidden. The
   pinned increasing order yields `(first,last,step)=(0,0,1)`.
3. `write_kind_of_flags false false false` returns `Write_plain`. Its
   unsupported flag combinations are not rewritten into ordinary stores.
4. The one-fuel loop retains its true dummy assertion and offset-zero address
   computation. It reads `pmpcfg_n`, then reads `pmpcfg_n` and `pmpaddr_n` in
   `pmpReadAddrReg`. The existing TOR grant returns `none` for Store Data.
5. The loop takes the full 64-bit slice of `new`. Prove this equal to `new`
   for arbitrary words; do not use a fixed machine snapshot or sample value.
6. `within_mmio_writable` evaluates the actual CLINT, signature and HTIF
   checks. Disabled HTIF still costs one `htif_tohost_base` read in the eager
   generated expression. The RAM interval and pinned configuration yield
   false, so no device-write path is taken.
7. `write_ram Write_plain ...` emits one actual `.writeMem 8` request with
   a present payload. The loop then combines its initial success value with
   the returned Boolean, marks the sole iteration finished, and returns.

Thus there are five register reads from four distinct registers before the
write event, with no register writes. There is no mstatus, current-privilege,
satp or TLB read in this particular API: Supervisor is an explicit argument.
Source anchors for the calculations are `Mem.lean:238–255,262–404`,
`SplitAccessUtils.lean:255–274`, `Pma.lean:349–414`,
`PmpControl.lean:211–224` and `Platform.lean:241–251,711–717`.

The exact request from `PhysMemInterface.lean:292–326` is:

```text
access_kind = AK_explicit { variety = AV_plain, strength = AS_normal }
va = none
pa = address
translation = ()
size = 8
value = some new
tag = none
```

Both the dependent event width and the declared size are eight. The program
is a present-payload write, not the absent-payload announcement builtin.
Metadata handling `__WriteRAM_Meta` is the actual pure unit definition.
The residual must remain defined on every V1 response:

```text
residual (Ok anyOptionalBool) = pure (Ok true)
residual (Err ())            = pure (Ok false)
```

In particular, this write error is not the read wrapper's exit behavior.
The native owned-RAM event rule proves that actual successful successors
use `Ok none`; it does not justify deleting the other syntactic response
continuations from the checked decomposition.

## Owned modules and structural boundary

Propose new `MachCSL/Logic/SupervisorWrite{Defs,Spec,Plan,Proofs,Link}.lean`
and `SupervisorWriteSTATUS.md`, with namespace
`MachCSL.Logic.SupervisorWrite`. The read owner is implementing the analogous
`SupervisorRead` prefix described in
[`supervisor-read-boundary.md`](supervisor-read-boundary.md). Names are
separate; neither task edits the other's files or `RegisterPlan`.

Use a local four-share footprint in the same order as the read proposal:
PMA, PMP configuration, PMP address, HTIF. All four shares may independently
be full, fractional or discarded; prove key uniqueness. The proof-side
boundary follows the agreed read design, specialized to writes:

```text
Boundary fp rs req program residual
  event:
    Boundary fp rs req (.impure (.writeMem 8 req) residual) residual
  prefix:
    RegisterPlan.Returns fp rs segment value rs →
    Boundary fp rs req (next value) residual →
    Boundary fp rs req (segment >>= next) residual
```

This is an inductive proposition about the actual free tree. Bind transport
keeps the exact residual after a caller continuation. The native fold is
proved by induction: register prefixes use `RegisterPlan.fold`, and the event
uses `TsoContextWriteWP.wp_write_normal`. The context, old word and incoming
reservation remain framed through the prefixes. The public checked-store
rule constructs its own `Boundary`; its caller does not supply one.

If generalizing the read boundary to an arbitrary dependent event is later
useful, do that as a separately reviewed refactor. It is not necessary for
this bounded store proof and should not delay or mutate the active read work.

## Proposed native resource theorem

For the four-cell footprint, let `cells rs shares` mean the existing native
register assertion. The intended `wp_checked_write` is:

```text
generationCertificate fixed gen era
  -∗ cells rs shares
  -∗ running era cpu ξ
  -∗ wordPointsto era ξ address (own 1) old
  -∗ resvFrag era cpu rr
  -∗ ▷ (∀ view,
        cells rs shares
        -∗ running era cpu ξ
        -∗ wordPointsto era ξ address (own 1) new
        -∗ resvFrag era cpu none
        -∗ viewLB era cpu view
        -∗ WP (hart gen cpu (continuation (Ok true))) post)
  -∗ WP (hart gen cpu
      (checked_mem_write (Physaddr address) 8 new (Store Data)
          PBMT_PMA Supervisor () false false false >>= continuation)) post
```

Its explicit pure hypotheses are the existing `TorRam rs`,
`RamRange address 8`, `rs htif_tohost_base = none`, a concrete matching PMA
region for the entire eight-byte range, and that region's overridden
`writable = true`. Alignment comes from the real full word assertion; it is
not an extra caller-supplied hardware fact. The old contents are arbitrary
and may already be dirty in this context. There is no pristine/empty-log,
current-memory equality, chosen-successor or global reservation-disjointness
hypothesis. Any incoming reservation `rr` is permitted.

The receipt's index is the actual event's unchanged pre-write CPU view,
not a newly chosen read view or the appended log length. The public existential
state abstraction expresses it through the guarded universally indexed
continuation, just as the underlying write WP does. The exact one-event
state theorem retains equality of all CPU views, one authored append, unchanged
registers/devices/image, and only the own reservation cleared. It does not
claim that other actors take no steps during the multi-event wrapper.

The guard is paid at the actual write node. On a blocked retry the old word,
context, register cells, reservation `rr` and guarded continuation remain
available for the same node. No store update is performed merely because
the instruction has reached the memory boundary. On success the native rule
pays the exact heap/TSO update, returns the new word and reservation `none`,
then follows the checked actual success residual. This is safety/partial
correctness, not a fairness or termination guarantee.

`Spec` records this public theorem. `Proofs` constructs both the physical
prefix and its native fold; `Link` constructs the actual `Spec` without
assumed subordinate contracts. No new camera, registry slot, metadata name,
readonly conversion or duplicate register authority is needed.

## Scope after the first freeze

Pure callback corollaries for `mem_write_value_priv_meta` and
`mem_write_value_priv` (`Mem.lean:586–598`) are reasonable only after the
checked-store core is green. They preserve the explicit Supervisor parameter
and introduce no new register reads. The first target is Store Data only.

`mem_write_value` additionally reads mstatus and current privilege and computes
effective privilege (`Mem.lean:602–609`; `HartSMem.v:3053–3097`). The actual
store instruction also runs `mem_write_ea`, which repeats the relevant
address/check prefix and performs the pure write-address announcement
(`Mem.lean:497–530`). Neither prefix may be omitted when later assembling
an actual instruction proof. Effective-address transformation, virtual
translation, the source tier-mapped word resource and full fetched STORE
execution are subsequent work, not hidden premises of this physical theorem.

Conditional PTE writes remain separate. `PtTreeAdue.v:111–120,1444–1496`
uses Store PageTableEntry, `supports_pte_write`, `con=true`, an actual
reservation snapshot and a conditional update obligation. Its generated
request is exclusive, its physical side has different reservation/view
behavior, and the page-table ownership carries A/D and publication duties.
The new rule does not turn that into a plain store or infer permission from
`writable`; it does not prove Sv39 writeback or consume canonical PTE pins.
AMOs, acquire/release stores, misaligned splitting, MMIO, arbitrary old-payload
visibility-free stores and instruction/cycle/function WPs also remain outside
this first boundary.

Validation will build every owned module, prove the singleton-loop address
and whole-word-slice equalities for arbitrary data, check complete emitted
request/residual correspondence, and audit physical declarations with all
opaque bodies, types and constructors. Only the existing standard three
Lean axioms are allowed; no native-decision axioms or generated-model edits.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
