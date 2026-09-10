# Working on the Lean port of MachCSL and xv6

Read docs/PLAN.md and docs/STATUS.md before choosing work. The completion target is
all supporting proofs and closed whole-system theorems over pinned kernel and disk
bytes, with Sail sub-instruction semantics, TSO, devices, and persistent crashes.
A buildable scaffold or an abstract safety theorem is not completion.

## Proof contracts and integration

- Keep definitions/specifications, generated code, proofs, and linking separate.
- Agree on owned files and theorem signatures before parallel proof work. Use
  isolated worktrees for overlapping changes. Do not edit another worker's files.
- Report missing lemmas and contract conflicts; do not silently weaken hypotheses,
  strengthen preconditions, change the kernel, or alter the model to finish a proof.
- Production proofs must have no `sorry`, `admit`, or new unreviewed axioms. Audit
  transitive axioms of theorem roots; text search alone is insufficient.
- Explicitly record semantic assumptions and unimplemented dependencies. Never
  describe a conditional theorem or a model-only lemma as xv6 verification.
- Crash/reboot preserves the durable disk; fs.img is used only at initial power-on.
- Keep generated outputs reproducible from immutable inputs. Never hand-edit them.
- Every task reports changed files, exact theorem names, commands and results,
  remaining obligations, assumptions, and next bounded task in shared status.
- Review difficult designs independently, including concurrency and vacuity. If a
  design stalls, checkpoint its failure and use a fresh agent with explicit goals.

## Attribution

Every outward-facing post under Jason's accounts (PR bodies, comments, issues,
emails, and project reports) must append:

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*

Preserve upstream copyright and license notices. Do not claim upstream authors
wrote the Lean port. Claude contributions must be identified in review records.
