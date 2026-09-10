# Independent power-on / fetched-instruction integration review

PASS: no soundness, thread-pool or state-witness defect found.
Reviewed `MachCSL/Machine/FetchIntegration.lean`, SHA-256
`57a48f0bf86c1f5fbbb3b678efb5ab4fd474687517a3a0b5a11422b5720285da`,
together with the previously reviewed actual-fetch witness and machine rules.
No production edits were required.

The generic lift is exact: `writeBack` changes the selected hart's registers,
view and reservation, together with shared local memory/devices/log, while
preserving the era image, generation, power and other harts' local data.
`othersReserved_writeBack` proves the union of other harts' reservation domains
is unchanged. `nodeStep_writeBack` therefore uses the original `NodeStep`
premises, not a weaker reservation environment. `writeBack_focus` and
`writeBack_twice` justify the endpoints and composition.

`nodeSteps_poolSteps` inducts over the real finite local relation and constructs
Iris `Language.Step.atomic` / `NSteps.cons` for every local event, retaining
arbitrary left/right thread context. The installed Iris atomic rule appends
forked threads after the existing pool suffix; its sequence rule concatenates
observations. These are the actual thread-pool relations exposed by the shared
image-parametric language, not a new proof-only simulator. The lift deliberately
chooses the same hart throughout and claims existence of that schedule, not
correctness of all interleavings.

The concrete witness starts from `bootState jalImage before`, uses the exact
CPU-zero register file produced by generated boot, and applies the actual loop
restart to select `cycle false`. The restart clears an already-empty reservation.
It then uses the checked RAM-backed JAL `NodeSteps`, returning to the same loop
expression. Its step count is strictly positive and its final record changes
only CPU zero's registers. PC/nextPC remain at the vector and minstret is 1;
all other workers' registers and shared post-boot state are retained.

`powerOn_fetchedJal` additionally starts from the actual singleton power-thread
pool with an explicit `before.power = false` premise. A real power-on transition
boots the machine and forks all eleven workers (eight harts, UART, disk, PLIC).
The subsequent schedule runs CPU zero and retains the power thread and all
workers, for an exact final pool of twelve entries. The only observation is
PowerOn; the total step count exceeds one. The durable disk is exactly the
pre-boot disk, not the repository's initial fs.img.

This is the complete concrete finite power-on/fetch/retire witness requested by
the early machine-code gate. It does not establish repeated-cycle invariance,
hart progress for arbitrary programs, arbitrary-interleaving safety, xv6 kernel
safety or Iris adequacy. The same language family also takes the separately
checked actual xv6 BootImage, so this fixture has not replaced the target
machine's semantics.

An independent enforced `Lean.collectAxioms` audit passed all 19 handwritten
integration proof roots; only `propext`, `Classical.choice`, `Quot.sound` occur
transitively. Audit driver/log:
`/tmp/xv6-lean-research/FetchIntegrationAudit.lean` and
`fetch-integration-review-axioms.log`. The earlier independent RAM-sensitivity
checks remain applicable to the imported fetch witness: absent RAM rejects the
evaluation, and changing only the JAL instruction bytes changes the resulting PC.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
