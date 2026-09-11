# Supervisor physical-prefix review

Coordinator review: pass for all three SupervisorPhysical modules. The reviewer
read the complete implementation, generated Pma/Mem branches, and the source
pma_class_grants/pma_allows_ram definition at RiscvFetchExec.v 88–165.

The allowed family explicitly covers two/four-byte fetches, eight-byte PTE
loads with either reservation flag, and ordinary eight-byte data loads. The
matched-region and selected-permission premises are exact projections required
by these operations. Arbitrary unrelated PMA attributes remain unrestricted.
Alignment yields the actual CannotSplit result; the data reservation assertion
is discharged by the supported-call constructor. The actual single PMA read
is retained with an explicit footprint fraction.

The priority wrapper's successful branch does not execute PMP. The separate
phys_access_check composition executes PMP first (configuration, configuration,
address), then PMA. These APIs are correctly distinguished. RAM classification
retains the eager HTIF read, with its disabled value owned in the footprint;
CLINT and signature checks are discharged from the actual model and bounds.
The mathematical positive RAM interval excludes modular endpoint wrap.

The independent fresh audit checked all 58 declarations, full types, opaque
bodies and constructors. Only the standard three axioms occur; there are no
unsafe/partial logical dependencies and zero excluded roots. Evidence:
SupervisorPhysicalAudit.lean and supervisor-physical-peer-audit.log under
/tmp/xv6-lean-research.

This is an aligned register-prefix proof. It supplies no RAM word, ownership
access callback, whole-state preservation, or full translation theorem. The
broader source integer-width PMA contract, writes, AMOs and misaligned accesses
remain outside the bounded supported family and are explicitly recorded.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
