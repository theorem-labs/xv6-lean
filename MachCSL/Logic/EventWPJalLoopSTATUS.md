# Native per-hart JAL loop

`EventWPJalLoop{Spec,Proofs,Link}` are checked and frozen. `registryJalLoopWPSpec` closes the actual infinite pure-node/restart/fetched-cycle loop at the common 23-slot native Iris registry, under the explicit static and current PMP snapshot preconditions and actual owned-register, code-byte/pristine, and reservation resources.

The proof uses native guarded recursion over every symbolic owned register table. The actual restart rule clears the reservation and quantifies over both clock choices. The actual per-cycle WP preserves CPU-owned cells and code resources, handling all counter configurations, overflow, interrupt pin results, and allowed TSO read views at their separate machine events. Its continuation invokes the guarded loop hypothesis at `cycleAfter`, using the proved static/snapshot closure. The returned `resvFrag none` is packaged back into `resvAny`; it is not dropped or assumed to survive reset unchanged. No finite execution trace or bounded evaluator alone supplies this infinite WP.

The proof imports only the per-cycle and restart contract vocabulary. The link supplies both actual implementations. The resulting theorem retains its real initial resources, runtime ghost names, explicit platform instance and current `SnapshotCovered` predicate. The latter still fixes PMP contents to the earlier concrete boot witness and has not been inferred from every arbitrary-preboot `BootFacts`. Universal OFF-only fetch, allocation/splitting for all eight harts, power-handler composition and whole-system adequacy remain separate obligations. Thus this is a genuine conditional per-hart infinite WP, not the closed JAL machine gate.

Validation: native link passed a 472-job dependency build. Fresh physical-origin audit covered all ten logical declarations in the three modules, including private helpers, with only `propext`, `Classical.choice`, and `Quot.sound`; no unsafe/partial logical dependency and no runtime-companion exclusions. Audit: `/tmp/xv6-lean-research/JalLoopWPAudit.lean`, log `jal-loop-wp-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
