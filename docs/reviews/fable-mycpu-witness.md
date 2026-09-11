# Fable eighth review: concrete Bare mycpu witness and capabilities

The following review was written by Claude Fable 5.1 through Claude Code,
requested model claude-fable-5-1 at max effort. All tools were disabled:
this is source review, not an independent build. The frozen packet contains
122 files and590737 characters; hashes are in fable-mycpu-witness-inputs.json.
The CLI returned success in361101ms, one turn, Fable-only model usage and
no delegated agents. Independent native builds and audits are recorded
separately. The coordinator's disposition addresses findings and scope.

**Verdict: approve. The narrowly stated Bare operational gate can close** once one wording defect in the pool statement is fixed, either by a trivial strengthening of `pool` or by rewording. No soundness blocker in the witness, the Off adapter, HartTp, or SupervisorBits.

I read the disposition and accept its three corrections. `phase_result` needs the reflexive `Phase entry 14` at the reference file, which is exactly what `MycpuBareWitnessResultProofs.result` now supplies, not `phase_zero`. HartTp is correctly an owned pinned GPR file over real cells, not a persistent ghost, and `actual_tp` is the right form of physical TP truth. The shared boot allocator extracts the text span only, and the rule is meaningful for any image satisfying its resources.

### What the witness establishes and what I checked

- **Every cycle is the actual generated cycle.** Each of the fourteen certificates first checks by kernel evaluation that `run 4 (cycle false)` on the exact prior local state equals the composed pure file `completeAfter (bodyFile entry k (checkpoint k))` with the expected memory, log, view and reservation. That equation is only satisfiable on the success path: a trap or an unexpected event would leave `run` at `none` or at a different PC, and the certificate would fail. This is the configuration-executability check round seven asked for.
- **Full register equality, not equality modulo ignored fields.** `ordered_core` gives the 173 data registers uniformly through `body_core` and `completed_core`; the seven control fields are checked individually by kernel reflexivity in every certificate. `checkpoint (k+1)` is therefore the exact register file, including `minstret = k+1`, which also confirms the increment flag is true under the configured counter registers.
- **Restart and order.** `Cycles.cons` inserts the real `restart_step` with `tick = false` before each cycle, and `cycles_steps` composes it into one `NodeSteps` from `.pure ()` to `.pure ()`. The checkpoint index sequence is forced by the actual PC progression, so the order is the machine's, not the bookkeeping's.
- **No memory oracle.** `run_sound` is stated for every fuel, program and state with only the view bound. Reads go through the existing `pauseRun_sound` at the current view; writes are accepted only when non-device, non-exclusive and with a present payload, and each is justified by `write_node` against `NodeStep` with an empty other-hart reservation set. Every other event makes `run` fail. The read cache is proved pointwise equal to `loadedRam bootImage` in `cached_image`, so the evaluator reads the real image.
- **Own-log reloads.** Both restores read at view zero and see the two stores only because `visible` admits own-authored messages above the view. That is the machine's TSO rule, and the certificates exercise it rather than assume it. The final view is zero and no reservation ever exists, matching the WP's `resvFrag none` at every boundary.
- **Final state and frame.** `values` fixes RA, S0, SP restored, `a0 = 0x80012568`, which is the CPU-array base plus three times 128, both saved words at entry values, and a two-message log. `code` proves all 34 fetched bytes untouched. `global_frame` and `global_views` show every other hart file, all devices, the image, reservations, power and generation unchanged. `result` and `hart_result` land the concrete run on the same public `Result` and `HartResult` the CPS exports.
- **Off adapter.** `partition` is a reversible separation equivalence over 53 distinct keys, with `footprint_unique` decided on the concrete list. The mstatus cell comes from `msOwn`, the six body GPRs from the pinned file, and the twenty-one controls from independent shares, so nothing is duplicated. SIE false is derived by ghost agreement with the off-token, MPRV, MXR and SXL from `MsFacts`, and TP from the pinned x4 cell. `reassemble` rebuilds the pinned file using only the body result's RA, callee-saved and stable-TP facts on owned keys, and `framed_entry` returns the fourteen untouched GPRs unchanged.

### Findings

**Blockers.** None.

**Required before the closure wording is accurate.**

1. **The pool is a singleton.** `pool` and `pool_positive` are stated on `[.hart 0 cpu (.pure ())]`, so the other seven harts and the three device workers are absent, not unscheduled. `focused_nodeSteps_poolSteps` is generic in `left` and `right`, and `.power :: powerFork 0` already contains `.hart 0 3 (.pure ())` in place. Instantiate with `left := [.power, loop 0 0, loop 0 1, loop 0 2]` and `right` the remaining forks, and the sentence "other harts unscheduled" becomes literally true. If you keep the singleton, the wording must say "single-thread pool" and rely on `global_frame` for the other harts.
2. **Say what the witness fixes.** Add to the wording: one specific `Platform` instance, reads always at the minimal permitted view, `Devices.initial`, and a synthetic `configured` state with zero register files on the other harts.

**Evidence gaps, not defects.** The base machine definitions `focus`, `writeBack`, `HartStep`, `MemoryOK`, `ReservationsOK`, `bootImage`, `loadedRam`, `bootByte_after_file`, `pmaBoot`, `TorRam`, `fetchRun`, and the whole native rule stack below the cycle layer are outside this snapshot. The witness chain above them is reviewable end to end, and the two evaluator lemmas it relies on are in the packet. The kernel certificates use `withTransparency .all` for the elaborator step; the assigned `Eq.refl` is rechecked by the kernel, which is what the trust rests on.

**Observations.**

- `Off.Result.saved` and `Off.Result.ra` are true by construction of `returnedMap`, which only rewrites indices 10 and 15. The substantive physical facts are `body.saved`, `body.ra` and `body.stable`, consumed by `returned_agrees`. The STATUS should say so, so a reader does not take the software-map clauses as independent evidence.
- The witness mstatus `0xa00000000` satisfies all ten `MsFacts` conjuncts and SIE zero. A one-line lemma stating `MsFacts (entry .mstatus)` would document that the concrete configuration is compatible with the Off adapter's entry, though no resource inhabitation follows.
- `namesOfEra` reads bit names from the era record, but nothing allocates ghost variables at those names; `attach` returns existential names. Off's precondition is therefore not producible from any current boot lemma, independently of the register values. The closure wording's "native Iris EntryConfig resource allocation OPEN" should name this bit-name installation explicitly alongside the running context and the supervisor register cells.
- The 21-key `controlFootprint` is computed by a filter and pinned by `control_list` at `rfl`; the count in `footprint_counts` is likewise reflexive. Good, no hand-maintained list can drift.

**Closure wording.** With the pool fix, the proposed sentence is accurate. I would state it as: native Bare `mycpu` CPS, plus an actual fourteen-cycle operational witness from an explicitly configured supervisor state on the pinned image, reaching the same exported result; boot reachability, era-name bit allocation, running-context and supervisor register-cell allocation, KPT tier, SIE capability, virtual free stack, the JAL wrapper, all six roots and cross-prover correspondence remain open; the witness fixes false clock choices, minimal views and one platform instance while the CPS admits every clock successor.

### Next source-faithful steps

1. **Regime-parametric cycle layer, then KPT `mycpu`.** The chain, `State` and `Reference` are translation-independent; only `MycpuFetch` and `MycpuMemory` bind to Bare configs. Abstract `MycpuCycle.Spec` over a fetch, load and store bundle indexed by regime and reuse `chain` unchanged. The KPT instance needs the shared table ownership and the walk boundaries you are building, including the A-bit write on first touch under the enabled bit 61, and both TLB hit and miss paths.
2. **Install the era-named bits at power-on.** Run `attach` inside era allocation so the returned names become the record's `supervisorInterruptEnable` and companions for each CPU, using the reset mstatus, which satisfies `MsFacts` with SIE zero. This makes `msOwnAt` and the off-token allocatable and removes one of the three inhabitation gaps.
3. **JAL-call wrapper in Bare.** One additional cycle writing `ra := P + 4` composed before `wp_function` gives the shape of `wp_call_mycpu_sconf_cs` and the first two-function composition at a return boundary.
4. **`push_off` from the disabled arm.** With SIE already zero the CSRRCI keeps the bit, `flip_four` at the same value covers the ghost tie, and the CPU-record words at offsets 120 and 124 are ordinary context words. This exercises a CSR write against `msOwn` without the enabled-arm handler resources, and is the natural bridge to the source's two-arm `SpecPushOff`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
