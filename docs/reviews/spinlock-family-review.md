# Independent review: seventeen-instruction spinlock family

Result: **PASS for the declared finite-plan scope.** This review was performed by
the Codex artifact-audit agent independently of the Codex logic agent who wrote
the seven `MachCSL/Machine/SpinlockFamily*` modules. No source correction was
required.

I read `Defs`, `Proofs`, `Arithmetic`, `Scalar`, `Control`, `Access`, `Plans` and
their status record completely, and checked their composition against the
actual generated instruction plans, `SpinlockCore`, `SpinlockCycle`, and the
concrete instruction image. The underlying model is the pinned paper artifact,
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`; this integration image is a new
validation program, not an xv6 theorem from the paper.

The boundary family distinguishes the current PC from the default nextPC after
instruction preparation and from the committed PC pair after retirement. Its
seventeen rows cover all decoded instructions. The CSR result is the actual
boot hart ID; unsigned comparison selects exactly CPUs 0 and 1. The other six
CPUs branch to and remain at index 16. Participant, base-register and constant
operand facts are retained precisely where later instructions require them.
Boot leaves unrelated general registers arbitrary. The underlying core retains
arbitrary PMP addresses, irrelevant configuration bits, interrupt pins and
counter values; both actual clock choices are covered.

The AMO plan retains separate exclusive-read and conditional-write events and
the exact selected write-mode eligibility. Its cases cover both binary old
values and all protocol successors: acquisition returns zero and the held
state, while a failed swap returns one and idle. The subsequent branch uses
these actual register results. The counter load, increment, store, non-draining
`FENCE rw,w`, and zero unlock store follow their generated instruction plans.
The arithmetic proof establishes low-word truncation after sign extension and
addition for every 32-bit word, including wraparound. No boundary reservation
is fixed to `none`. Both actual PLIC pin-update arms preserve the family.

`instruction_plan` covers all seventeen finite indices. `cycle_plan` composes
actual fetch, decode, execution, retirement and optional clock update; it does
not collapse the instruction into an atomic machine step. The protocol
relations in these plans acquire their resource meaning through the separately
reviewed native event fold and protocol callbacks. These seven files alone do
not establish an operational schedule, annotated-pool coverage, holder
exclusion, a positive interference witness, or the closed machine gate. The
status record states these limits accurately.

Independent validation completed:

- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Machine.SpinlockFamilyPlans`
  passed all 448 jobs.
- A fresh physical-origin audit of all seven modules checked all 154 logical
  declarations, including private helpers, with zero excluded runtime
  companions. The replay explicitly uses `info.value? (allowOpaque := true)`
  to include theorem bodies. It traversed statement and proof dependencies and inductive
  constructors; only `propext`, `Classical.choice` and `Quot.sound` occurred,
  and no unsafe or partial semantic dependency occurred.
- The independent driver and output are
  `/tmp/xv6-lean-research/SpinlockFamilyIndependentAudit.lean` and
  `/tmp/xv6-lean-research/spinlock-family-independent-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
