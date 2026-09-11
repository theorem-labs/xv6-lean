# Independent supervisor-clock review

Result: PASS for the four frozen `SupervisorClock{Defs,Spec,Proofs,Link}.lean` modules and their STATUS contract. This is an independent source and event review by the sail-audit agent. No production files changed.

Compared against pinned xv6iris `HartMCycle.v:329–590,693–715,883–946`, `MinstretInv.v:341–350`, actual generated `LeanPaperStock/Platform.lean:378–395,534–547`, and the imported read-only callback and native register-plan rules.

The clock plan retains every actual generated read independently through `Plan.readAny`. Its fold uses the real machine `wp_read_any`: it quantifies over the value produced by an actual register step and preserves the existing state interpretation. It does not choose a register value, erase a read, or require ownership of unowned configuration, timer deadline, or interrupt-pin registers. Full ownership is required for each write, and the unique footprint supplies a checked extraction and restoration of the affected cell.

Only `mcycle`, `mtime`, and `mip` can be written. The proof includes inhibited and enabled counter branches, privilege filtering, modular 64-bit increment, unconditional time increment, MTIP update, enabled and disabled STCE branches, optional STIP update, and changed-mip callback reads. The callback includes `sig_meip`, `misa`, and the conditional `sig_seip` read; it does not frame PLIC-owned pins as owned cells. Both optional tick choices are explicit. `OffClock` concerns the symbolic footprint file; it makes no claim that unowned physical registers remain fixed across interleavings.

The native WP returns all supplied footprint resources with their original fractions at an existential successor file. `clockRes_iff` matches the source's three existential full 64-bit cells. Its reverse direction fills only the otherwise unowned symbolic fields with defaults. `wp_clockRes` restores this same linear resource under either optional choice. The continuation still requires its own WP; this is not a proof of fetch, retirement, the entire cycle, or software correctness. The source's `minstret_inv = emp` is correctly distinguished from its linear `clock_res`.

The documented backend difference is real: pinned Rocq `rv64d.v:23011–23025` uses monadic short-circuit conjunction, while generated Lean reads `mcyclecfg` even when CY is inhibited (and analogously reads `minstretcfg` for retirement). The Lean proof retains that extra event. This review approves its resource contract for the actual Lean program, not event-tree equivalence with Rocq.

Fresh validation: replayed `/tmp/xv6-lean-research/SupervisorClockAudit.lean`. All 37 physical-origin logical declarations pass the transitive standard-three-axiom allowlist; type, opaque-body, and datatype-constructor dependency traversal rejects unsafe and partial declarations. Zero roots were excluded. The clock plan, both-choice WP, existential-resource WP, and concrete native specification have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
