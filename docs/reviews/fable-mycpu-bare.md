# Fable seventh review: native Bare mycpu

Requested model `claude-fable-5-1`, effort `max`, same reviewed session,
all tools disabled. This is source review, not an independent build.
The frozen input contains81 files,393695 characters; input hashes are
recorded in fable-mycpu-bare-inputs.json. The CLI returned success in
1177085ms, one turn, Fable-only model usage.

**Verdict: approve.** The Bare `mycpu` CPS is a faithful physical-resource analog of `wp_mycpu_sconf`, the fourteen-cycle chain is in the right order with the right widths, the stack round trip is carried by owned context words rather than assumed, and I found no per-step success premise, duplicated cell, or fixed clock value. No soundness blocker. Two small additions are needed before the STATUS may call the Bare gate closed, and several base rules are outside this snapshot and are recorded below as evidence gaps.

### What I checked and confirmed

- **Instruction order and widths.** The fourteen `decoded`, `normalized`, offsets and widths match `CodeMycpu.v` row for row, including the two base instructions at offsets 14 and 18, `c.addi4spn` expanding to an immediate of 16, `c.mv` expanding to `ADD` from `x4` with no read of `x0`, and `c.jr` expanding to `JALR` with `x0` as link. `stepWidth` and `pcAt` agree with `MycpuDecode.address`. The AUIPC base plus the ADDI immediate give the stated `cpus` address, and `valid_hart` is closed by `rfl` for all eight CPUs.
- **Fetch footprint is honest.** Ziccif reads four bytes at every four-aligned PC, so compressed rows at aligned addresses fetch a neighbouring halfword and the last row fetches two bytes past the body. The 34-byte span, `footprint_complete`, and `base_aligned` account for this. Both fetch branches of the generated `fetch` are handled; the second two-byte read is shown unreachable rather than assumed.
- **No hidden per-step premise.** Only `EntryConfig` is public. Every intermediate `MycpuCycle.Config`, read and write config, and return config is derived from `stable_config` through `phase_stable` and `phase_address`. `Completed` is universally quantified in every continuation, so all post-clock files are covered.
- **Clocks and interrupts are arbitrary.** `CoreEq` ignores exactly PC, nextPC, minstret and its flag, mcycle, mtime and mip. Ticks are arbitrary at entry and at every restart. `mie &&& ~~~mideleg = 0` with SIE false blocks every interrupt in supervisor mode regardless of mip or the two pins, and `dispatch_plan` is stated without any mip value.
- **Stack save and restore.** `phase_stack_address` fixes both slot addresses from `reference_sp` for cycles one through twelve. The two stores rewrite the owned words to entry `ra` and `s0`. The two loads are applied with those owned words as their value argument, so the reference load values are supplied by the resource, not assumed. The words return at entry values, and old scratch contents are correctly not claimed.
- **Own-write readback is justified the source way.** The reload is a context-word read, whose value comes from `wordPointsto` at the running context for any view. That is the port of `TsoCtx` clean-byte ownership and is stronger than the own-author rule I suggested in round six.
- **Framing and duplication.** The twenty-eight cycle keys and the eleven frame keys are proved distinct as thirty-nine. Every share in `activeShares`, `memoryShares` and `returnShares` maps onto a single cell of the twenty-eight. The frame is never split, and `calleeFrame_result` retargets it using the proved preservation. By key counting, all sixteen `stableRegisters` sit inside the twenty-eight, so `Stable` is physically meaningful.
- **Residual WP scope.** The continuation is the ordinary next-cycle WP at `retPC (entry.x1)` with the cells at the actual post-clock file. That is the shape of the source's `WP Loop` continuation. Internal laters are absorbed, which only weakens the rule.
- **Address geometry.** Both RAM ranges come from the word resources through `word_range`, and modular SP arithmetic is retained. No sixteen-byte alignment or no-wrap premise is added.

### Findings

**Required before "closed", both small.**

1. **Operational witness.** The theorem is a rule and cannot itself show that `EntryConfig` together with `TorRam`, `pmaBoot` and Bare `satp` is a configuration the pinned model executes through. Run the fourteen cycles from one concrete `EntryConfig` file with `fetchRun` and `pauseRun`, using `write_node` for the two stores and `read` steps for the two loads, exactly as the spinlock witness did. Add the pure lemma that `reference entry 14` satisfies `Result entry`, which `phase_result` already yields from `phase_zero`. Together these guard against a self-contradictory premise set or result.
2. **STATUS scope lines.** State that no allocation lemma yet produces `running ξ` or register cells for a supervisor-mode entry file, that only `shared` and the stack words are reachable from `allocate_shared_boot`, and that the rule is image-generic while only the `Xv6.Machine.bootImage` instantiation is meaningful.

**Evidence gaps, not defects.** The snapshot omits `SupervisorFetchRead`, `SupervisorRead`, `SupervisorWrite` and their `Boundary.fold` rules, the `TsoContextRead` and `TsoContextWrite` implementations, `wp_complete_clock`, `wp_restart_fragment`, the register event rules, `SupervisorBareFetch.fetch_boundary`, the Bare read and write program boundaries, `SupervisorAddress.program_plan`, `try_step_factor`, `TsoContextWord.aligned`, and the three sub-footprints. I verified composition and bookkeeping against their stated interfaces only. On the source side only `SpecMycpu`, `ProofMycpu` and `CodeMycpu` were supplied, so `sie_cap_gpr`, `ktier`, `kernel_text` and `HartTp` are compared by their use in those files.

**Observations.**

- The Bare regime is not artificial. Real xv6 boot calls `printf`, hence `acquire`, `push_off` and `mycpu`, on hart zero before `kvminithart` installs the kernel table. Proving that reachability is a boot-path theorem, not part of this gate.
- The configured `menvcfg` sets bit 61, so hardware A/D updates are enabled in the pinned model. This confirms the round-six concern for the KPT step and should be recorded next to the PTE work.
- `wp_hart` takes `entry.x4 = cpu` explicitly. The source discharges the same read through the `HartTp` invariant. A per-era persistent `tp` fact allocated at boot is the faithful replacement and is small.

### Next integration step and the boot question

**Recommendation: make the cycle layer regime-parametric, then instantiate KPT.** The chain, `State`, `Reference` and `Config` derivations do not depend on Bare translation. Only `MycpuFetch` and `MycpuMemory` do, through `SupervisorBare` configs and `SupervisorAddress.Config rs .Bare`. Abstract `MycpuCycle.Spec` over a bundle of fetch, load and store rules indexed by a translation regime, prove `chain` once against the bundle, and keep the Bare instance as is. The KPT instance then needs exactly the translated fetch and data boundaries with PTE reads and the atomic A/D writeback, which the in-progress `Sv39Walk`, `KptLeaf` and `SupervisorPteAD` files are building toward. This avoids a second fourteen-case chain and gives a source-faithful tier-indexed theorem. The JAL-call wrapper for `wp_call_mycpu_sconf_cs` is a cheap parallel item that also exercises two-function composition at the return boundary.

**Is an inhabited real-boot setup needed?** Not for this gate. The source has no per-function witness either; whole-system adequacy supplies inhabitation there, and here the register cells for a supervisor-mode entry file can only arise by executing the boot path. What is needed is the operational witness above, which certifies the configuration without any Iris resource, plus the honest STATUS line that resource-level inhabitation of the precondition remains a boot-path obligation.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
