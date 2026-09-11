# Universal boot projection review

Codex independent review: PASS for the stated static projection. Reviewed the frozen `BootUniversalDefs`, `BootUniversalRun`, and `BootUniversalProofs` against `Machine.Run`, `RegisterRun`, `BootProgram`, and the `boot_facts` register clause in pinned `iris/RiscvLang.v:1335–1356` (`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`).

`registerRun_unique` is conditional on an actual successful total evaluator run. It follows every completed auxiliary `Run` one event at a time. Evaluator success excludes all unsupported events; register reads determine the result and preserve the full view state, and register writes determine the updated register file while preserving RAM/devices. The finite fuel bounds the proof evaluator, not the semantics of `Run`.

`projection_raw` is kernel reflexivity on the actual board/reset/firmware program with arbitrary initial registers and arbitrary vector/hart. Separately proved numeric MISA/status facts avoid expanding large model terms during symbolic reduction. `run_static` combines those equalities with uniqueness, and `bootFacts_static` extracts each hart's arbitrary preboot witness from the actual `BootFacts` predicate. It never replaces that witness with `zeroRegisters`.

The thirteen returned static fields are exactly explicit conclusions. PMP configuration and addresses, counter inhibit/filter settings, and other unlisted registers remain unconstrained; this theorem does not establish an entire canonical register file, instruction execution, or a WP. The image-parametric vector is intentional; the source kernel instance uses its fixed entry vector.

Fresh module-origin audit (including private helpers): 52 logical declarations, no excluded runtime companions, only `propext`, `Classical.choice`, and `Quot.sound`; no unsafe/partial declaration in the combined logical dependency cone. In particular, `registerRun_unique` uses only `propext`; `bootFacts_static` uses the standard three. Raw audit: `/tmp/xv6-lean-research/BootUniversalAudit.lean`, log `boot-universal-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
