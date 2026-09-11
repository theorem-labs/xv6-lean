# Independent supervisor physical-store review

Reviewer: the Codex artifact-audit subagent, independently reviewing the
lean-logic subagent's five `MachCSL/Logic/SupervisorWrite{Defs,Spec,Plan,Proofs,Link}`
modules and STATUS. The reviewer previously implemented the parallel read
boundary and supplied two elaboration suggestions, but did not author or edit
these write modules. Baseline: xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476` and actual generated LeanPaperStock.

Source/proof review passed without a requested correction. The declared scope
is a native aligned eight-byte ordinary Data checked store at explicit
Supervisor privilege, with the existing registered-context resource payer.
It is not the full source supervisor store instruction rule.

The source `HartSMem.v:2930–3027` (`swp_checked_mem_write_S`) stages PMA,
singleton split, PMP, writable MMIO and the real ordinary RAM write using four
register resources. The implementation follows those stages on the generated
program, replacing the source's generic `Wobl`/`Hwrite_node` abstraction with
the implemented full context-word write rule. `HartSMem.v:3029–3103` additionally
reads mstatus/current privilege for `mem_write_value`; this larger wrapper is
explicitly excluded. Source `TsoCtx.v:2572–2592,4346–4371` supplies the context
store/map/window resource shape, through the existing native context layer.

Checked generated definitions include `Mem.lean:262–404,534–598`,
`PhysMemInterface.lean:292–326`, `Platform.lean:241–251,711–717`, the existing
supervisor TOR plan, and the native TsoContextWriteWP/MemoryWriteWP integration.

- The actual PMA table is read and matched, PBMT_PMA permissions are checked,
  and the non-conditional Data assertion is retained. Alignment yields
  CannotSplit; the successful priority wrapper issues no extra PMP check.
- PMP uses the source-positive supervisor TOR configuration, not the Machine
  all-off branch. There are two configuration reads and one address-vector
  read. Later entries and irrelevant bits remain as allowed by that existing
  contract. The reused TorRam package includes R/X as well as W; this store
  consumes the W grant.
- Writable MMIO preserves the eager HTIF read and its width-at-most-eight
  expression. Disabled HTIF, actual RAM bounds, CLINT exclusion and the pinned
  signature configuration discharge this branch. Five reads use four distinct
  fractional cells, with no register writes in the constructed prefix.
- The singleton loop keeps its pure assertion and exact offset/order behavior.
  Polymorphic zero-offset addition and full 64-bit extraction are proved for
  arbitrary addresses/words. The emitted V1 event retains all metadata:
  explicit plain/normal access, VA none, PA, unit translation, size eight,
  present payload and absent tag.
- `OneWrite` quantifies over every successful optional response payload and
  separately retains `.Err ()`. These tails are respectively `Ok true` and
  `Ok false`, exactly as generated; the read-side Exit behavior is not reused.
  The explicit-privilege wrapper equalities reduce only actual pure callbacks
  and preserve the program's exceptional branches.
- `Boundary` contains only actual event and existing unchanged-register prefix
  judgments. Its native fold performs structural induction, uses the genuine
  RegisterPlan fold, and invokes the implemented context write at the event.
  The public theorem constructs the Boundary itself and derives alignment
  from word ownership. It accepts no hypothetical access implementation,
  successor preservation theorem, empty-log premise or fixed old-memory fact.
- The native context payer retains full heap metadata and TSO authority. Its
  guarded update happens in the successful write branch. MemoryWriteWP's
  actual blocked branch recurs with the untouched reservation and unopened
  update continuation. There is no assumption that other harts' reservations
  are disjoint, no reservation cleared on blocking, and no termination claim.
- Success appends one message authored by the actual hart, changes the exact
  bytes, leaves all CPU views unchanged and clears only the own reservation.
  The returned lower-bound receipt is the event-time view, not the new log
  length. The same context, new full word and original register shares return.
  The event inversion/effect corollaries expose these exact alternatives;
  they do not prohibit interleavings during the preceding register prefix.
- Existing generation handling accounts for power changes. Fixed observation
  state is restored using the actual silent step. No new camera, name,
  invariant instance or separate state interpretation is allocated here.

Independent validation passed on the final five-module snapshot including both
explicit-privilege callback equalities. `tools/lake.py build
MachCSL.Logic.SupervisorWriteLink` passed 529 jobs. The fresh
`/tmp/xv6-lean-research/SupervisorWritePeerAudit.lean` selected all physical-origin
declarations from the five modules: 97 logical declarations, zero exclusions.
It checked collected axioms and traversed all types, opaque bodies using
`value? (allowOpaque := true)`, and inductive constructors. Only `propext`,
`Classical.choice` and `Quot.sound` occur, with no unsafe/partial semantic
dependency. Explicit checked-boundary, native-rule, implementation-link,
actual-step and pure-wrapper axiom queries also passed. File SHA-256 values
were unchanged between review and validation. Evidence:
`supervisor-write-peer-{build,audit}.log` and
`supervisor-write-peer-snapshot.sha256` in the same research directory.

This review retains the declared limits: no effective-privilege/address-announcement stage,
virtual translation, conditional PTE/A-D update, AMO, misaligned/MMIO access,
fetch/STORE instruction WP, complete source Wobl family or whole-kernel claim.
Full Rocq/Lean semantic correspondence remains a separate repository obligation.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
