# Replayed paper Rocq baseline

The original `arxiv-v1` development at `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476` built successfully in an isolated checkout and opam root on 2026-09-11. All 2,104 tracked files remained unchanged. All six source roots then passed separate statement-dependency and proof-assumption queries: twelve successful compiler processes. This certifies the recorded source build and reports; it does not establish the Lean port or a cross-backend semantic correspondence.

The six proof-assumption logs are byte-for-byte identical. Rocq prints thirteen entries: dependent functional extensionality, `xv6iris_extras.resv_matches`, `xv6iris_extras.resv_is_valid`, and ten native primitives (`PrimInt63.int/sub/lsr/lsl/lor/land/eqb`, `PrimString.string/get/cat`). Statement-seed assumption reports print the same twelve primitive/platform entries without functional extensionality. The original printer category `Axioms` is retained; primitives are not relabeled as arbitrary user axioms.

[summary.json](summary.json) records exact source statements, locations/hashes, scoped response counts and assumptions. [audit-manifest.json](audit-manifest.json) preserves successful commands, elapsed times and raw-log hashes. Its log paths are portable; the original command paths remain unchanged as historical evidence. `PaperStatement0.v` through `5.v` and `PaperAssumptions0.v` through `5.v` are the exact query files. Full stdout/stderr logs are included, together with deterministic gzip archives of the four build logs and compiler dependency files. `artifact-hashes.json` covers the archived evidence files.

The environment is recorded in [paper-opam-resolved.txt](paper-opam-resolved.txt) and the switch export: OCaml 5.3.0, Rocq/core/runtime 9.0.1, stdlib 9.0.0, Iris 4.4.0, stdpp/bitvector 1.12.0 and Sail-stdpp 0.20.1. [paper-rocq-build-results.json](paper-rocq-build-results.json) contains all four Makefile-generation and build commands/exits; the Iris build took 2,923.776 seconds. The source hash manifest and integrity result are separate from compiler results.

The compiler-generated local import union has 1,314 modules (1,292 Iris): 1,312 from SystemAdequacy and 1,314 from SystemUartAccepted. Independent review checked every edge against the four dependency files. Every reached source is active in its corresponding _CoqProject. This is module import closure, not declaration use. The raw graph's `all_dependencies_active` means active-project membership only; the normalized parser replaces it with an explicit field. No external .vo prerequisite was emitted in these local rules, although external Iris/stdpp/Sail libraries are required.

Rocq's `Print All Dependencies` prints constants/assumptions, omits ordinary constructor and inductive entries, and provides no direct edges or canonical kernel identifiers. Its collector internally traverses encountered mutual-inductive constructor types, but does not separately traverse every constant's declared type. The statement seed's body is the elaborated theorem type; this avoids seeding the root proof body. Separate `Print Assumptions root` queries traverse available proofs and print only the assumption frontier. A complete declaration type/body graph and the Lean/Rocq semantic relation remain open. See the [independent review](../../reviews/paper-rocq-replay-peer-review.md).

From the repository root, regenerate the normalized report without rerunning Rocq:

```sh
python3 tools/upstream.py xv6iris
python3 tools/paper_audit_report.py --self-test --require-complete \
  --manifest docs/upstream/rocq-replay/audit-manifest.json \
  --source-root .upstream/xv6iris \
  --import-graph docs/upstream/rocq-replay/paper-compiler-import-graph.json \
  --output /tmp/paper-rocq-report.json
```

To replay the compiler, use a separate clean checkout at the recorded commit and a separate opam root/switch with the recorded package versions. Run each recorded `coq_makefile -f _CoqProject -o CoqMakefile` in its own directory, then the ordinary model/kernel/user builds followed by Iris, using the recorded commands with your isolated paths. These targets compile the tracked model/kernel/disk data without regenerating it. Run the archived query files from the Iris directory with its _CoqProject load paths and warning flags. Compare source hashes again after compilation. The query files separate each theorem's proof assumptions; statement files contain two printer commands whose response boundaries the parser conservatively checks.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
