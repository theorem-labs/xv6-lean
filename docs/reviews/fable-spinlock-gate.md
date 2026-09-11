# Sixth Fable review: complete spinlock gate

Reviewer: Claude Code, `claude-fable-5-1`, max effort, tools disabled.
The review received the complete source packet; it did not independently
run Lean. The text below is Fable's response, preserved verbatim.

**Decision: approve.** The safety root, the operational exclusion, and the positive witness are all present with the scopes you list, and I found no unsound definition, assumed callback, or ambiguous annotation in the supplied sources. Two small additions are needed before the STATUS may call the gate closed. The kernel plan is sound in content but has its critical path in the wrong place.

### What I verified in the gate

- **Label determinism is real.** `nextCursor` is a function of the pre-state, post-state, program, and old label. Blocked versus committed writes are separated by log length, blocked versus successful exclusive reads by the post reservation, and restart by the boundary PC. `transition_functional` follows, so `scheduled_holder_exclusion` is universal over every annotation consistent with `Transition`. That closes the round-five meaningfulness gap.
- **The real-machine statement carries no label.** `reachable_boundary_exclusion` takes only expression membership and register PCs. Labels, the schedule, and the invariant are built inside.
- **Coverage uses inversions, not callbacks.** Each `Head` constructor is discharged by an inversion of the actual step. Those lemmas are implications from the real relation, so they can only be proved if they enumerate every arm.
- **Workers frame correctly.** PLIC writes only the two pins, which `OwnedMatch` excludes. UART changes only its device field. The reset disk step is shown to be the identity even through the wild arm. Power-off bumps the generation and power-on requires power off, so occurrence uniqueness survives cycles.
- **The owner's converse is proved, not assumed.** `selected_owner_phase` derives it from `Shape.current` through Nodup of the permutation. The failed-swap case refutes ownership of a `reserved` cursor through `HolderPosition`.
- **Lock word and owner agree by construction.** `Words.lockValue` is defined from owner presence. `head_node_scenery` shows the only lock-word writers are the three plan-permitted requests.
- **The view bound has its kind fact.** `swap_write_exclusive` is a checked `rfl` and `winning_append` uses it. The counter read uses the chain from the counter timestamp through the acquisition position to the chosen view.
- **The fence is genuinely inert.** `afterBarrier_nondraining` handles the general case. In the witness the concrete `fencePost` reduces to the old view by kernel evaluation.
- **The witness matches the semantics.** I traced all seven appends, both blocked checkpoints, the views at each stage, and the four register-file tables against the instruction table. All agree. The second-round counter load reads the timestamp-two message at view five. Final expressions are post-write continuations with PC still at the unlock word, as you state.
- **The witness matches the annotation.** By inspection the labels run idle, reserved zero, held at position one, loaded, stored, idle at position four on CPU zero, and reserved one, idle, reserved zero, held at position five, stored, idle at position seven on CPU one. No mismatch with `PhaseOK` or `WordsOK`.
- **The certificates are kernel checks.** Assigning `Eq.refl rhs` to a goal `lhs = rhs` makes the kernel decide the two sides by evaluation. That is only as strong as the absence of opaque definitions on the evaluation path, which the full-opaque audit covers.
- **No callback premise in safety.** `safe` takes only the powered-off, generation-zero facts and the run. The initializer is a theorem.

### Required before the STATUS says closed

1. **Window inhabitation.** No supplied theorem shows `Holds` is ever true on a real run, so the exclusion conclusion lacks the non-vacuity certificate that safety has. Cheapest route: stop the witness after two work cycles using `cyclesRun_sound` with two rounds, which leaves CPU zero at `.pure ()` with PC at the third body word, lift with `annotate_run`, and apply `boundary_holds`.
2. **One root theorem.** Compose, on the witness run, safety at the final configuration under `SpinlockWitness.platform`, the annotated exclusion from `annotate_run`, the inhabitation lemma, and the final-state facts. The dependency audit then has a single root.
3. **Scope lines in the STATUS.** The PC corollary holds only at `.pure ()` boundaries. The window theorem is the principal property. The witness uses no clock ticks, minimal views, no power cycle, and leaves six CPUs unscheduled. Uniqueness is relative to the occurrence-indexed schedule, not the erased trace.

Follow-ups that do not gate: a positive execution of one parked CPU reaching the loop boundary, so the `2 ≤ cpu` clause of `At` is inhabited; a mixed corollary that one CPU at a body boundary excludes every other annotated holder; unifying the two `initialState` definitions.

### Kernel plan critique and next bounded theorem

- **The critical path is the supervisor substrate, not LockSet.** `mycpu` needs no held set, rank, lock camera, SIE arm, or context crossing. LockSet and LockRank at slot 26 are correct leaf work and may proceed in parallel. They should not be reported as progress toward any function theorem, and their real cost is the deferred connection of eight authorities to a boot era.
- **Settle A/D bit behavior first.** xv6 maps kernel pages without Accessed or Dirty bits. If the pinned walker writes those bits, the first touch of every page is a store event inside a fetch or load, authored by the hart and appended to the TSO log. PTE storage is then mutable with a monotone three-valued fact, and any `CodeUnwritten`-style invariant needs a PTE clause. If the walker faults instead, xv6 could not run, so the source resolved this inside its translation tier witness. Read that definition, and whether the model has a TLB register with `sfence.vma` semantics, before designing `reads` for table walks.
- **`mycpu` forces one new TSO rule.** A plain store does not advance the view, so reading back the saved `ra` from the stack cannot be justified by a view receipt. It needs an own-author read rule, the native form of the source's own-write witness. Name and prove it before the WP.
- **`holding` is heavier than its instruction count.** The nonholder answer needs the eight-byte owner window with per-agent own-last records and the kernel lock invariant, not the test protocol. Schedule it after `TsWin`, not directly after `mycpu`.
- **Migration enters at `push_off`.** Its stack setup precedes the CSRRCI, so it can be interrupted and migrated before the clear. `mycpu` and `holding` enter and exit with SIE false. State those two in a hart-pinned supervisor WP and later prove that WP is the SIE-false specialization of `wp_next`, instead of porting the interrupt fixpoint first.
- **The doc's numbers check out.** The AUIPC and ADDI pair yields the stated `cpus` address from the stated entry. The AMO, CSRRCI, CSRRSI, and fence words decode as described. The `noff` and `intena` offsets match a 128-byte CPU record.

**Next bounded theorem.** Prove `mycpu` in a hart-pinned supervisor WP. Premises: every valid CPU, arbitrary caller registers with `tp` equal to the CPU, SIE false, privilege S, each kernel table tier, the actual PMP configuration, `mie` and delegation as at boot, two writable stack words, and the checked kernel bytes at the actual entry. Conclusion: PC equals the entry `ra`, `a0` equals the CPU record address, `ra` and `s0` restored, other callee-saved registers unchanged, the two stack words returned writable with unspecified contents, no other memory event, and the running-context token returned unchanged. Milestones in order:

1. Supervisor fetch and translation plan for the fourteen words, including compressed decode and the A/D decision. This is prerequisite certification, not the port.
2. Own-author read rule and stack ledger rules.
3. The WP and its Link theorem, with LockSet landing in parallel.

**Disposition.** Merge the gate as assembled. Add the inhabitation lemma and the root theorem before changing the STATUS wording. Keep the LockSet branch open but reorder the plan document so the supervisor substrate and the A/D question head the critical path. Record that the exclusion theorem is generic in `Platform` while the witness fixes one instance, and that neither cross-prover correspondence nor any whole-xv6 target is affected by this gate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
