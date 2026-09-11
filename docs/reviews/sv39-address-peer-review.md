# Independent actual outer Sv39 address review

PASS for all six Sv39Address modules. The coordinator reviewed the eight
pure and three native contracts, all private/public proofs and native Link
independently of their author. The approved interfaces remain unchanged.

The canonical branch preserves the real seven register reads: effective
privilege, translation-mode selection, repeated SATP read, and separate MXR
and SUM reads. Config owns actual Supervisor/SXL/SATP facts; effective
privilege preserves the fetch exception to the MPRV requirement. The native
SATP accessors supply root and zero ASID. Nested VPN extraction is proved
equal to bits 12–38, not replaced by an unchecked cast.

Noncanonical inputs take the actual five-read branch and access-specific
page fault. The complete suffix handles every translation result and error,
including extension errors, preserves PBMT/payload, and constructs the full
44-bit PPN plus 12-bit offset before zero extension. No read or error arm is
erased. The canonical native fold explicitly requires the exact remaining
translation-body WP and returns the same three cells before it; the complete
KptAddress residue wrapper must discharge that boundary.

Native/registry build passes 750 jobs. Owner and fresh coordinator audits
cover all 110 physical declarations, types, opaque bodies and constructors:
standard three axioms only, zero exclusions and no unsafe/partial dependencies.
The coordinator traversal disables exporting. Evidence is
Sv39AddressRootAudit.lean and sv39-address-root-audit.log under
/tmp/xv6-lean-research. Full residue composition, translated instruction
wrappers and boot publication remain subsequent layers.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
