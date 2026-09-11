# Actual supervisor Sv39 address wrapper

The six-module implementation proves the exact outer `translateAddr`
boundary. Defs/Spec were reviewed at the 452-job checkpoint before proof
implementation; the unchanged contracts are now constructed by native
links, building at 750 jobs. The 110-declaration full opaque/type/constructor
audit passes with zero exclusions. The owned prefix is
`Xv6/Kernel/Sv39Address*`.

The relevant source is all of `KptShare.v` lines 320–482, especially
`tlb_res_pt_translateAddr_at`, and the generated `Vmem.lean` from
`get_satp`/`translateAddr` at lines 549–593. Also read were actual
`effectivePrivilege`, `translationMode`, `is_shadow_stack_access`,
`translationException`, and the existing supervisor Bare plans. Source pin:
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`; model pin:
`23dcf8fd923eb8a1958795393d2975632aa940b2`.

The actual program is `translateAddr (.Virtaddr address) access`. Supported
access is precisely the existing kernel leaf family: fetch, ordinary Data
load/store and Data AMOSWAP with arbitrary aq/rl flags. The sufficient
configuration requires current Supervisor privilege, SXL=2, and the exact
three-field `KptResidue.SatpRooted root satp`: mode bits 8, ASID zero and
actual PPN equal to root. Effective privilege additionally requires either
instruction fetch or MPRV=0, reusing `SupervisorBare.Effective`. Fetch therefore
has no unnecessary MPRV restriction. MXR and SUM remain arbitrary and are
read separately. No MENVCFG, MISA, fixed-reset or pointer-masking assumption
is introduced at this outer boundary.

The footprint is the existing three-cell supervisor footprint:
`mstatus`, `cur_privilege`, `satp`, each with an explicit `DFrac`. It is
disjoint from KptTranslate's six physical controls/TLB cells. The full source
residue owns SATP and PMP/TLB separately; later residue composition must split
and reassemble those exact resources. This checkpoint neither duplicates
those cells nor allocates another register authority.

The eager read sequence is preserved:

| Stage | Actual register reads | Result |
| --- | --- | --- |
| Effective privilege | mstatus, cur_privilege | Supervisor |
| Translation mode | mstatus for SXL, satp for mode | Sv39 |
| `get_satp 39` | satp again | actual complete SATP |
| Noncanonical VA | no further reads | actual access-specific page fault |
| Canonical VA | mstatus for MXR, mstatus for SUM | exact translation arguments |

Thus the invalid-address path has five reads and the canonical prefix has
seven, before any TLB or PTE events. Shadow-access classification is the real
program call; supported payloads prove it false. Both SATP reads remain.
There is no register write or memory guard in this prefix.

`Canonical` is the source sign-extension check expressed by exact BitVec
extraction: the input equals the 64-bit sign extension of its low 39 bits.
`vpn` extracts bits 12–38. For canonical inputs, the residual is exactly
`KptTranslate.program 0 tree (vpn address) access (mxr rs) (doSum rs)`,
with `SatpRooted (PtTree.base tree)` deriving the root argument. The pure
`Boundary` datatype records only actual register plans followed by this
whole residual program. It contains neither an assumed transition-preservation
callback nor an assumed translation result.

The suffix keeps the actual `translationException access error` call on
**every** error constructor, including extension errors. Supported-access
classification is proved from the actual generated cases, not assumed. Successful results concatenate
all 44 PPN bits with the low 12 input offset bits, then zero-extend the 56-bit
quantity to 64 bits. PBMT and extension payload are preserved. The suffix
accepts arbitrary returned PPN/PBMT and all translation errors; it does not
specialize the translation body to successful PBMT_PMA results. The pure
`pageFault`/`accessFault` classifiers are specified only under `Supported`,
so their catch-all value is never used as semantics for unsupported payloads.

Eight pure contracts cover footprint uniqueness, actual mode and SATP plans,
root/ASID extraction, actual exception classification, the full result suffix,
and canonical/noncanonical program decomposition. Three native contracts
fold the canonical prefix, the complete noncanonical error path and the
result suffix. The canonical splice explicitly takes the WP of the exact
translation residual with its actual suffix after returning the same three
cells. This is an intermediate compositional theorem, not a closed translation
claim or software-success oracle. The remaining WP must be constructed from
KptTranslate's native specification in the subsequent full residue wrapper.
The noncanonical and suffix contracts need only their final continuation.

The source absorption theorem operates on memory-indexed resources inside
an invariant. This prefix does not replace that theorem with an atomic
whole-function model: the existing native translation layer opens shared
resources at its actual memory events. All its hit/miss outcomes, A/D guards,
reservation effects and receipts remain outside the prefix and are preserved
by the exact residual program. SATP switching, VA address transformation,
shared-tree lookup, source claim/residue extraction, and kernel boot
reachability are separate obligations. No camera or registry change is needed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
