# Independent spinlock core-register review

Reviewer: OpenAI Codex subagent `lean_logic_audit`, independently reviewing
coordinator-authored `SpinlockCoreDefs` and `SpinlockCoreProofs`. Result:
**PASS for the stated register-family preservation scope**.

`Core` includes the seven exact access-static fields, plus `mie`, `mideleg`,
`elp`, active hart state, all PMP-off facts and the actual CPU's hart ID. It
leaves PC, operands, counter settings, pending interrupts and PMP addresses
unconstrained. `boot` obtains every field from the universal actual-BootFacts
proofs, including `BootHartId`; it does not specialize to zero preboot registers.

The general write lemma exhausts the actual register datatype and permits only
the 15 listed volatile/operand/pin keys. None changes a Core field. The scalar,
CSR, branch, enable/prepare, PC tick, retirement and clock preservation lemmas
reduce to these same register writes, with both conditional outcomes covered.
The clock and retirement arithmetic need no non-overflow condition.

The PLIC lemma uses the actual `PlicStep` constructors, preserving the Core of
the selected CPU after either pin write and every other CPU through the exact
`updateHart` lookup. It does not incorrectly claim that PLIC leaves the whole
register file unchanged. These constructors are the pinned
`RiscvLang.v` PLIC actions already implemented in `Machine.DeviceSteps`.

The finish projection lemmas show both final PC and nextPC equal the completed
instruction's nextPC. Retirement/clock preserve that pair. `finish_atInstruction`
correctly retains the separate premise that this nextPC is an in-range
instruction address; it does not prove that arbitrary operand values or
instructions establish reachability of such a target.

Rebuilt the frozen target (429 jobs). A fresh audit checked all 79 declarations
from the two physical modules, including private helpers, and their full
type/body/constructor dependency cones. Only `propext`, `Classical.choice` and
`Quot.sound` occur; no unsafe/partial semantic dependency and zero exclusions.
Evidence: `/tmp/xv6-lean-research/SpinlockCoreAudit.lean` and
`spinlock-core-audit.log`.

No corrections requested. Operand/phase invariants, actual memory instruction
postconditions, complete PC reachability and all-pool protocol coverage remain
separate obligations. The Core family is a reusable component of those proofs,
not a closed spinlock gate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
