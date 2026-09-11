# Supervisor Bare translation review

Coordinator review: pass for all three SupervisorBare modules. The complete
implementation was read against the actual generated translateAddr,
translationMode, architecture and effectivePrivilege definitions and the exact
SRegime.v 182–185 supported-access family.

Config owns the source supervisor privilege, SXL=2 and satp Mode=Bare fields
through three explicit fractional register cells. Translation retains all four
actual reads: mstatus, current privilege, mstatus and satp. Fetch leaves MPRV
and MPP unrestricted; the other source-supported accesses use MPRV=0.
AMOSWAP acquire/release annotations remain arbitrary. ASID, PPN, all address
bits and the unowned TLB are unrestricted. No misa read or extra hardware
premise is added: the actual supervisor architecture branch uses SXL directly.

The result is exactly the input physical address, PBMT_PMA and unit metadata,
with the same symbolic footprint file. Native RegisterPlan.fold supplies the
existing event-by-event WP interpretation; unowned physical registers are not
asserted equal across interleavings. The source full translation resource also
carries PMP and other ambient ownership, which must remain available at the
later physical-access boundary.

The independent fresh audit checked all 55 declarations and their complete
types, opaque bodies and constructors. Only the standard three axioms occur;
there are no unsafe/partial logical dependencies and zero excluded roots.
Evidence: SupervisorBareAudit.lean and supervisor-bare-peer-audit.log under
/tmp/xv6-lean-research.

This closes only the source Bare branch. Pointer masking in data wrappers,
Sv39/TLB/PTE/A-D behavior, memory events and full supervisor instruction WPs
remain additional obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
