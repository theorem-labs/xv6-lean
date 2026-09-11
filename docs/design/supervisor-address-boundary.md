# Supervisor data-address transformation

Root owns SupervisorAddress{Defs,Spec,Plan,Proofs,Link}+STATUS. Exact source
HartSMem.v:375–430,484–550 proves mode-parametric transformation identity.
Read actual PmUtils210–257, Vmem.translationMode426–447, and VmemUtils.transform_effective_address.

One four-cell fractional footprint owns mstatus/current privilege/menvcfg/satp.
For Data load/store, Supervisor, MPRV-clear, MXR-clear, disabled menvcfg PMM,
SXL2 and an actual decoded satp mode, prove the six actual read plan and native
WP returning the arbitrary64-bit input virtual address unchanged. The mode is
an arbitrary decoded SATPMode, including Bare and Sv39; physical and virtual
zero-mask transforms are proved identity, not assumed. Keep eager applicability
mstatus read and actual menvcfg read; other fields are arbitrary.

Pure mode and mask equations are architectural inputs, not a subordinate
translation or WP oracle. The primitive config derives actual effective
privilege itself. Separate code contains main definitions/statements/proofs/link.
No new camera or memory resource is required. Base-register address formation,
actual vmem wrappers, full memory instructions, KPT translation and fetched
function correctness remain later composition work.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
