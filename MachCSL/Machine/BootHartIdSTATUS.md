# Universal hart identifier

`BootHartIdProofs.projection` kernel-checks the actual board/generated boot
program's hart-ID result for every arbitrary preboot register file, vector and
hart value. `run_hartid` uses registerRun_unique to transfer that checked result
to every completed source-shaped Run. `bootFacts_hartid` applies it to each actual
BootFacts witness, and `bootFacts_selected` proves the unsigned less-than-two
selector chooses exactly CPU zero and CPU one.

The general machine still has eight CPUs. This does not assume that other CPUs
are absent or unscheduled, and it does not prove their program branches or a
spinlock. The new projection supplements the existing StaticBoot facts without
changing them or imposing a canonical preboot file.

Validation: the 154-job component build passes. A fresh physical-origin audit
checks six logical declarations with standard foundational axioms only and no
unsafe/partial dependency or runtime-companion exclusion. Independent review
passed; see docs/reviews/boot-hart-id-review.md. Logs: boot-hartid-build.log and boot-hartid-audit.log under
`/tmp/xv6-lean-research/`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
