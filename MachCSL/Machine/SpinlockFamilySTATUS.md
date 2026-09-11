# Spinlock instruction-boundary family and finite cycle plans

The seven `SpinlockFamily*` Lean modules prove the concrete seventeen-boundary
register/protocol family for the actual 68-byte integration image. `boot`
starts every hart at index 0 from **any actual `BootFacts` witness**, including
arbitrary preboot register contents. `instruction_plan` covers every decoded
instruction; `cycle_plan` composes actual fetch, decode, execution, retirement
and both clock choices and returns another boundary in the family.

`Core`, operand facts and the PC pair are separate. `Ready` records the real
instruction prefix's default nextPC; `Completed` records an in-image nextPC;
cycle completion commits both architectural PC fields. No constraint is added
to the boundary reservation argument. Arithmetic helpers prove low-word
sign-extension/truncation and modular increment using ordinary kernel proofs.
The seven scalar cases compile in 4.4 seconds in the final build.

The boundary rows are:

| Index | Extra operand/protocol facts |
| --- | --- |
| 0 | Idle; unrelated operands unconstrained |
| 1 | Idle, x5 = actual hart ID |
| 2 | Idle, x6 = 1 exactly for harts 0 and 1 |
| 3 | Participant, idle |
| 4 | Participant, idle, AUIPC result x10 = lock + 12 |
| 5 | Participant, idle, x10 = lock |
| 6 | Participant, idle, x10 = lock, x14 = 1 |
| 7 | Same, x15 = 1 before AMOSWAP |
| 8–9 | Failed swap: idle/x15 = 1; successful swap: held/x15 = 0 |
| 10 | Held before counter load |
| 11 | Loaded, x16 = sign-extended counter word |
| 12 | Loaded, x16 = sign-extended modular counter + 1 |
| 13–14 | Stored, before and after actual FENCE rw,w |
| 15 | Idle after unlock |
| 16 | Idle, hart ID at least 2, self-loop |

The participant bound persists through indices 3–15, x10 through 5–15, and
x14 through 6–15. Actual AMO read and conditional write remain separate
`EventPlan` events. Both binary read results and every protocol write successor
are covered; no old value or schedule is selected. Counter and unlock stores
use the exact frozen protocol modes and request metadata. The actual fence is
non-draining. Both actual PLIC pin-update arms preserve every hart's family.

The proofs use the frozen generated instruction plans, not copied instruction
semantics. The source/pin is the same actual generated model recorded in
`SpinlockAccessSTATUS.md` and `SpinlockCycleSTATUS.md`. This theorem supplies
finite plans to the native WP fold; it does **not** by itself prove the native
cyclic WP, annotated-pool `Covers`, operational holder-window exclusion,
interference witness or the closed two-hart gate. It adds no model guard,
atomic instruction collapse, ghost authority or native invariant world.

Validation: `SpinlockFamilyPlans` builds successfully (448 jobs). The fresh
origin-based audit of all seven modules traverses private declarations,
statements, proof terms and inductive constructors: all 154 logical
declarations passed with only `propext`, `Classical.choice` and `Quot.sound`,
zero excluded runtime companions and no unsafe/partial dependency. Evidence lives in
`/tmp/xv6-lean-research/SpinlockFamilyAudit.lean` and
`/tmp/xv6-lean-research/spinlock-family-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
