# Coordinator disposition of Fable reviews

Both requested Claude Code reviews completed with model `claude-fable-5-1` and
`--effort max`; both returned **APPROVE WITH REQUIRED CHANGES**. Returned reports
and minimal invocation metadata are preserved beside this document. Approval is
of the architecture, not a claim that the port or its remaining gates are done.

| Recommendation | Disposition and evidence |
|---|---|
| Paper tag versus current upstream | Keep `arxiv-v1`. Both final reviews withdraw the initial HEAD recommendation because newer sources change machine semantics. |
| Native Iris and direct proof port | Adopted; pinned Iris builds and its generic adequacy passes the transitive axiom audit. No reverse Rocq-to-Lean proof translator is assumed. |
| One-instruction gate, then concurrent spinlock | Required before broad function-proof work. Parameterize the same machine language by boot image; final roots instantiate the paper image. |
| Non-vacuity and durable crashes | Required: reducibility, execution witnesses, satisfiable initialization, discriminating filesystem predicates, justified self-loops, preservation of durable disk. Conditional boot links do not close this gate. |
| Image/decoder measurements | Packed numeric pages now support ordinary kernel-checked input-byte facts. The benchmark and limitations are recorded separately. Whole-image equivalence, ELF loading, instruction decoding and initialization remain open. |
| Audit scope | Module-origin coverage and an unused-axiom rejection fixture are implemented. Stronger computational-definition and closed-root audits are implemented, with eleven compiled positive/negative fixtures. Standard axioms remain the only proof allowlist. |
| Generator provenance and full model gate | Compiler source/release identity, binary digest, adapter revision and exact arguments are recorded. Full generation and instruction compilation pass against the free runtime. Six entry cones and a concrete JAL execution have independent checks; semantic correspondence remains open. |
| Platform hooks | Pure reservation predicates must be explicit parameters. Unbound effectful hooks must have a distinct stuck event with an empty result; they cannot be silently implemented as harmless values. |
| Outcome correspondence | Required: a transcription of relevant Rocq outcomes, payload/result equivalences and an arm-by-arm step-rule table. Tests do not replace this obligation. |
| Functor slots and sealed module contracts | Required before function specifications; conventions are recorded with exact theorem targets. |
| MIT notice for xv6 images | Implemented in `LICENSES/xv6-riscv.txt`. No license is invented for xv6iris or lean-sail. |

## Corrections and unresolved semantic recommendations

The revised review suggests giving Lean natural/finite choice requests no step
arm. **That is not adopted as an established correspondence.** Rocq's erased
integer result admits valid as well as invalid range choices. A proof that invalid
choices eventually get stuck does not by itself permit deleting valid outcomes.
The existing syntactic scan suggests these requests are unreachable from the
configured CPU/reset entry points, but it is not a checked certificate. We require
a complete generated dependency analysis and a justified reachability argument,
or an explicit compatible interpretation. Any excluded request must have an
explicit obligation; no silent narrowing of the paper's machine is acceptable.
The optional Lean write payload also requires builtin-level treatment: pinned
Rocq returns pure `Ok None` for an absent payload. The runtime now reproduces
that behavior; source review and tests passed. Present payloads still need the
request-field mapping described in `../Sail-correspondence.md`.

The revised review saw a temporary 136-file compiler output before it was removed.
That directory was incomplete after an interrupted run; its existence and lack
of textual `sorry` hits were not successful generation or compilation evidence.
A later uninterrupted stock generation exited successfully. Only completed and
checked artifacts are counted in project status.

The first review's universal supervisor-hart writer claim was withdrawn: disk
DMA legitimately writes RAM. Its early suggestion that finite conformance tests
replace cross-backend correspondence was also withdrawn. Reversible isolated
toolchain setup is already authorized by the user's request; it does not require
an additional permission flow.

## Performance gate

For the pinned kernel and disk, input header, selected page-boundary and bounds
facts must kernel-check with ordinary proofs and no custom computation axiom.
Use a 60-second, 2-GiB per-file development measurement as an initial warning
threshold, recording host/compiler/thread configuration; do not weaken statements
or replace proof checking with executable tests to pass it. Measure decoder facts
separately before generating an instruction catalog. CI's full build remains
limited to 30 minutes. These engineering thresholds are not theorem hypotheses.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
