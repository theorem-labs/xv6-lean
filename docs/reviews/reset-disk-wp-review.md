# Independent reset-disk WP review

Result: **PASS for the stated reset-device specialization**. Reviewed the
complete `Machine/JalDevicesDefs.lean`, `JalDevicesProofs.lean` and
`Logic/ResetDiskWP{Spec,Proofs,Link}.lean` read-only against paper pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

Source correspondence checked:

- `RiscvLang.v:530–610`: all seven disk actor constructors, especially the
  arbitrary-write malformed-queue arm, independent cache drain, and IRQ latch.
- `VirtioModel.v:299,421,1522,1679,1724,1824,1880`: queue liveness, reset,
  pop, completion, capture, drain and malformed-chain gates.
- `RiscvLang.v:boot_facts/prim_step`: actual reset fact, live/dead workers,
  empty/nonempty publication alternatives and reservation preservation.
- `RiscvPtsto.v:2083–2226`: current-era device halves, fixed generation and
  registry authority, observation interpretation and native WP instance.

`DiskReset` is an existential equality to the actual reset function, not a
replacement device or restricted transition relation. The predecessor's
entire durable disk and capacity remain arbitrary. Disabled queue liveness
excludes completion/capture/pop/wild writes; an empty cache independently
excludes draining; the zero ISR excludes the Virtio interrupt-latch arm.
The proof analyzes every actual actor constructor. It does not rely on the
existence of the idle arm to dismiss nondeterministic alternatives.

The global `disk_thread_idle` proof then forces the publication write set
to empty and the log to its old value. Overlaying the empty map preserves
RAM. Both actual live and dead disk arms therefore return exactly the same
expression and full state, with no events or forks. `uart_preserves_reset`
and `boot_reset` use the actual actor/boot definitions; neither asserts that
all hart programs preserve reset.

`reset_or_dead` derives its disjunction from actual fixed-state generation
and registry agreement. The live branch opens the current era and compares
the actual device authority half with the caller's reset fragment; the
stale branch refutes actual liveness. It does not assume that a selected
arbitrary state is reset. `wp_reset_disk` places the client fragment under
its guarded induction hypothesis, retains it through the real step, and
uses exact successor uniqueness to restore the complete power and trace
interpretation. Native NotStuck reducibility, mask close and the required
later are all present. Its arbitrary Empty-valued postcondition and final
registry instance are the same ones used by the other machine WPs.

Independently reran the build of `ResetDiskWPLink` and `EraStateLink`: 426
jobs passed. The separate all-declaration audit is
`/tmp/xv6-lean-research/ResetDiskIndependentAudit.lean`, with output in
`reset-disk-independent-axioms.log`. It checks all 25 public and private
JalDevices/ResetDiskWP declarations transitively and permits only
`propext`, `Classical.choice`, and `Quot.sound`.

No correction was required. This is an independently proved feasibility
lemma, not a verbatim replacement for production `wp_disk_loop`: active
queue protocol invariants, arbitrary DMA safety and the complete eleven
worker pool remain separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
