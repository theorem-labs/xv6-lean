# Actual seven-write two-hart interference execution

The six `SpinlockWitnessRelease{Defs,Certificates,State,Local,StateProofs,PoolProofs}.lean` modules finish the requested finite interference schedule through the existing actual `NodeSteps` and `PoolSteps` relations. `powerOn_seven_messages` starts with the sole power thread in any powered-off state, using the earlier concrete reset witness. `concrete_seven_messages` supplies an explicit powered-off state and platform; initial devices and their durable medium remain arbitrary parameters. There is no proposition premise on this concrete execution witness.

The resulting actual log contains these seven writes, in order:

| Author | Address | Word | Meaning in this schedule |
|---|---|---|---|
| CPU 0 | lock | 1 | Successful acquisition after exclusive read0 |
| CPU 0 | counter | 1 | First actual load/increment/store |
| CPU 1 | lock | 1 | AMO commits after returning old1; acquisition failed |
| CPU 0 | lock | 0 | Previously blocked unlock now commits |
| CPU 1 | lock | 1 | Successful retry after exclusive read0 |
| CPU 1 | counter | 2 | Second actual load/increment/store |
| CPU 1 | lock | 0 | Final unlock |

Both unsuccessful blocking events are paid actual transitions: CPU 1's first exclusive read is blocked by CPU 0's zero snapshot, and CPU 0's first unlock is blocked by CPU 1's one snapshot. `scheduled_conflicts` exposes these exact pool checkpoints and blocked steps on the linked execution. The earlier prefix theorems count both steps before their respective retries. The old1 AMO itself does commit its write; “failed” denotes the acquisition result and the subsequent taken retry branch, not a failed RAM-write event.

`final_values`, `final_log`, `final_log_authors`, `final_reservations`, `final_disk`, `final_generation`, `final_pool_length`, and `final_other_registers` prove the exact final lock0/counter2, seven messages and authors, no held reservations, unchanged durable disk, same live generation, twelve retained pool entries, and unchanged boot register files for CPUs 2 through 7. Those six harts have not been scheduled in this witness. Both active harts remain at their exact generated continuations immediately after successful unlock writes; the last instruction tails are retained, not replaced with synthetic termination.

## Checked execution and source scope

Twenty-one separate closed ordinary-kernel certificates check the actual failed-AMO tail, three fetched retry instructions, retry read and successful write boundaries, successful-AMO tail, four fetched counter-work instructions, counter write, non-draining fence and final unlock prefixes/tails. Eight additional direct kernel equalities check actual flat-memory values at the four final stages. Every extracted read/write/barrier continuation is tied to a successful exact classifier, including all request metadata; defaults cannot establish those certificates.

The actual taken BNE returns to instruction 6 at `0x80000018`, which reloads the AMO operand from `x14`, before instruction 7 retries the AMO. The expected dependent register files retain both the ordinary sequential `nextPC` write and the later taken-branch overwrite. The certificate caught and corrected an initial expected-boundary error; no generated semantics or previously checked instruction plan was changed.

Each evaluation interval is lifted by the previously proved `pauseRun_sound` or `cyclesRun_sound` with the actual TSO image, authored log, selected current view and complete reservation. Successful exclusive reads use the actual flat memory and advance to the current log top; successful writes update flat memory, append one authored message and clear only their own reservation. Plain writes and `FENCE rw,w` retain the current view. The native safety theorem and abstract protocol annotations are not execution premises.

This uses the pinned `iris/RiscvLang.v:mnode_step` (line 799 onward), hart lifting and power-fork relations at `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, with actual generated Sail execution of the checked 68-byte integration image. The existential platform/reset choices do not restrict the separately proved universal machine model. This is an integration execution certificate, not an xv6 filesystem or kernel theorem.

## Validation

`PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Machine.SpinlockWitnessReleasePoolProofs` passes all 437 jobs. Certificates took 25 seconds, local operational proofs 9.9 seconds, final state proofs 1.2 seconds and final pool proofs 3.5 seconds. A concrete nested reservation overwrite initially triggered expensive conversion; the final proof factors it through the abstract `overwrite_empty` lemma and explicitly supplies the compact local states. Large diagnostic probes were stopped and are not validation evidence.

The fresh physical-origin audit checks all 187 logical declarations in all six modules, including private helpers. It traverses types, opaque theorem bodies with `info.value? (allowOpaque := true)`, and inductive constructors. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Two compiler-generated total-recursion runtime companions are excluded as roots after checking their safe source owners; the complete logical dependency cone contains no unsafe or partial declaration. No `sorry`, new axiom, native decision procedure, unchecked certificate or preservation oracle was introduced.

Evidence: `/tmp/xv6-lean-research/SpinlockWitnessReleaseAudit.lean`, `spinlock-witness-release-audit.log`, `spinlock-witness-release-pool.log`, and `spinlock-witness-release-state.log`. The latter records the final successful certificate build before the later state-framing fix; the pool log records the final complete build.

*Authorship note: this was researched and written by an AI coding agent (OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is posted from this account.*
