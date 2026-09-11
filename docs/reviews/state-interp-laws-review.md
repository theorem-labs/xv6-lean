# Independent fixed-state interpretation laws review

Result: all five laws pass after the linking correction described below.
Reviewed frozen `StateInterpDefs/Spec/Proofs/Link` against the paper source
at `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The prior definition and
era-allocation reviews cover the underlying complete record, resource
conjunctions and component allocation.

`generation_cases` extracts both actual counter bounds. The birth receipt
excludes an unborn generation; the started receipt excludes the
current-generation/powered-off case. Its result is precisely a strictly
older generation or actual `ThreadLive`. This matches the case analysis in
`RiscvExec.v:766–805` and cannot turn a live hardware failure into an
arbitrary dead-thread stutter.

`live_era_access` reads the persistent registration against the actual
registry authority and equates the complete registered record with the
current existential era. It returns that exact era's interpretation and a
wand rebuilding the fixed power interpretation at the same state. The
counter resources, durable disk, registry authority and exact domain are
retained. This is the source live-era selection argument at
`RiscvExec.v:802–810`.

`power_off` performs the native generation increment, returns its persistent
death receipt and preserves the fixed sized disk authority, start counter
and complete registry. Actual `powerOff` retains the entire disk and advances
generation while clearing power. The start count therefore remains unchanged.
Dropping the per-era interpretation is the source affine PowerOff behavior
(`RiscvAdequacy.v:725–783`). This law covers the power interpretation only;
it does not claim an observation update or a power-thread WP.

`power_on` requires the actual image-parametric `BootShape`. Its disk
preservation equation transports the fixed durable authority. It advances
the start counter, allocates the actual new machine-era resources, inserts
the full record at the exact fresh generation key, and returns born,
started and persistent registration receipts together with all declared
machine boot clients. The domain proof preserves exactly all prior
generations and adds the new one. This matches the corresponding portions
of `RiscvAdequacy.v:833–912,954–985`; auxiliary kernel/crash/custody tokens
and the trace update remain separate as declared.

`initial_off_alloc` requires the actual initial power to be off and
generation to be zero. It allocates the fixed counters, empty registry,
sized durable disk authority/full fragment and both observation halves.
The history premise is actual `ObservationsOK`, and its whole-trace equation
is `history ++ future`. This generalizes the source's empty-history setup
(`RiscvAdequacy.v:1516–1578`) only to a history already satisfying that
invariant. It allocates no current era or per-era disk map. The supplied
step/thread indices are immaterial because the interpretation explicitly
ignores them.

The first reviewed link only instantiated `StateInterpSpec`, whose power-on
and initialization fields still accepted `EraSpec` and `DiskSpec` arguments.
The owner added `registry_power_on` and `registry_initial_off_alloc` in
response. These concrete wrappers now supply the proved era/disk contracts;
their theorem types contain no unproved component-spec premise. The generic
specification intentionally retains those dependency parameters.

Independent validation after that correction:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.StateInterpLink
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/StateInterpAllocationAudit.lean
```

The 406-job build passes. The separate all-declaration audit accepts only
`propext`, `Classical.choice` and `Quot.sound`, including both concrete link
wrappers; output is
`/tmp/xv6-lean-research/state-interp-allocation-independent-axioms.log`.
This review made no production edits; the owner supplied the link correction.
These results are allocation and ghost transition laws, not complete machine
lifting WPs or final adequacy.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
