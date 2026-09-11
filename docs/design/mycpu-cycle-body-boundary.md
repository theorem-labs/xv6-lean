# One register bundle for mycpu cycle composition

The four native body contracts preserve one unique 28-cell footprint.
It contains MycpuActive's fourteen cells (with full PC), five full GPRs
RA/SP/S0/A5/A0 and fractional TP, the four retirement cells, three full
clock cells and fractional hart-state. Other control shares remain
independently supplied. The footprint has no duplicate register keys.

This is the unchanged actual nine scalar, four memory and one JR body
behavior, using a wider common resource bundle. Native proofs widen the
checked register plans or concrete read/write boundary and fold directly
on that bundle; there is no temporary duplicate sub-footprint and no
fresh ownership allocation. Loads update exactly RA/S0. Successful stores
retain all registers and clear reservations; blocked retries preserve the
old word/reservation. Read views, word fractions, real context resources,
actual false-store Boolean tail and error Exit remain unchanged.

The pure setupMembers, completeMembers and clock_members discharge the
existing retirement interfaces on the same bundle. Four kernel equalities
connect actual MycpuActive.executeTail to these body programs and the real
Step_Execute wrapper. Generic associativity and case analysis preserve the
single ExecuteAs redirection, including every possible second result.

The public Spec comprises four native CPS rules: scalar, store, load and
return. Each conclusion runs the actual body; final continuation obligations
are ordinary WPs. There is no unproved body-correctness premise. These
contracts do not yet run the preceding dispatch/fetch or following retirement,
clock/restart, and do not claim complete function or source KPT correctness.
The source inputs and body boundaries remain those independently reviewed
for MycpuScalar, MycpuMemory and MycpuReturn. Actual source SIE capability,
virtual stack tiers and the fetched cycle still need composition.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
