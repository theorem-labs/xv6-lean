# Actual mycpu cycle and restart

Frozen four modules: MycpuCycle Defs/Spec/Proofs/Link. Four native rules
`wp_scalar`, `wp_store`, `wp_load`, `wp_return` compose the actual setup,
full dispatch/fetch/prepare/body, successful postlude, optional clock and
real restart. Their target is `MachCSL.Machine.cycle tick`, the source
riscv_step body, not the generated standalone Functions.loop. `actual`
and `nativeSpec` discharge the complete four-field Spec. The families
cover the fourteen indices already checked by CycleEntry.index_complete.

The exact CycleBody 28-cell bundle, arbitrary source control fractions,
actual running context, allocated discarded 34-byte text span and original
reservation are reused. No cells, names, cameras or timestamp ownership
are allocated. Memory families additionally use the real context word:
full old ownership for stores, arbitrary original fraction for loads.
Source Active.Config, HART_ACTIVE and body Config are stated at the
original file. Pure started_* proofs transport them through the sole setup
write to minstret_increment. The existing Entry proofs then handle nextPC
preparation and actual instruction effects.

The before-finish file is the exact Entry family result at started rs.
Each family proves hart-state remains active before applying real postlude.
The continuation receives Shell.completed of that exact file, which
preserves every off-clock field relative to completeAfter (actual PC
transfer and conditional minstret increment). Clock fields mcycle, mtime
and mip remain existential as in the reviewed clock plan; neither current
nor next clock choice is restricted. Actual restart clears reservations
for every family, including initially held reservations in load/scalar/
return cases.

Scalar/return rules require two guards, paid by fetch and restart. Memory
rules require three, paid by fetch, data event and restart. Additional
register/clock steps are not used to inflate this advertised guard budget.
The final continuation receives the entire register bundle/context/span,
reservation none, fetch receipt and (for memory) the data receipt and exact
updated or preserved word. No ordering between receipts is asserted. It
must prove only the next ordinary cycle WP for every nextTick; no current
body, fetch-result or preservation correctness premise remains.

Source/program boundary: actual Machine.Node.cycle/NodeStep restart,
generated try_step/postlude, pinned RiscvExec.wp_hart_restart:1007 and all
CodeMycpu instructions, through the previously reviewed Entry and Shell
proofs. Their factors retain waiting, interrupt, fetch-error and execution
failure branches. This cycle component does not establish supervisor/SIE
entry ownership, KPT translation, virtual stack claims, the complete
mycpu function or ABI result, an unconditional infinite execution, or
whole-kernel adequacy.

Validation: build passed 703 jobs; final Proofs 2.3s and Link 1.1s. Fresh
physical-origin audit checked all 63 declarations in the four modules,
including private helpers, types, opaque bodies with allowOpaque=true and
inductive constructor fields. Standard propext/Classical.choice/Quot.sound
only, zero exclusions, no unsafe/partial logical dependency. Evidence:
`/tmp/xv6-lean-research/MycpuCycleAudit.lean`,
`mycpu-cycle-{build,audit}.log`, `mycpu-cycle-frozen.sha256`.
Defs/Spec signatures remain those approved before implementation; no
previous implementation, generated source or umbrella was edited.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
