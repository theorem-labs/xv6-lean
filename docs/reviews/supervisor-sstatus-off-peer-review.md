# SupervisorSstatusOff independent peer review

PASS for all eleven declared contracts. No semantic correction is required. The independent Codex sail-audit agent read all six frozen implementation files, their design and STATUS, and the corresponding source and generated definitions. The implementation was authored by the artifact-audit agent. No implementation or PushOffCsr file was changed.

## Source and generated-model correspondence

Compared pinned `iris/WpGprCsrwCommon.v:240–301`, `WpGprCsrwC.v:1362–1429,1675–1702`, and `WpSieFlipBits.v:289–345` at source revision `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. Inspected actual generated `SysRegs.lean` definitions of `lowest_supported_privLevel`, `have_nominal_privLevel`, `legalize_mstatus`, `lower_mstatus`, `lift_sstatus`, and `legalize_sstatus`, plus `PlatformConfig.lean` support and virtual-memory queries. Checked the reused ten-conjunct `SupervisorBits.MsFacts` definition.

The pure `legalized old value` exactly follows the source symbolic update order and supported-platform specialization: supported S/U fields, nominal MPP or User fallback, XS forced Off, actual FS/VS legalizers, and SD recomputed from the resulting extension state. Fields not updated remain from `old`; writable saved ELP fields come from `value`.

The critical model condition is correct: **`hartSupports Ext_Zicfilp = true`**. `legalize_mstatus` directly uses that support query for both SPELP and MPELP. It does not inspect current MENVCFG.LPE. Arbitrary saved SPELP and MPELP must therefore remain, and both the definition and proofs preserve them. There is no zero-ELP premise.

The S-view mask is exactly the complement of 64-bit value 2. Lower-view projection and the bitwise clear identity establish that an already-zero SIE leaves this view unchanged. The lift/lower and legalized-self proofs compose to exact equality of the complete 64-bit status under source MsFacts and SIE=0. Consequently the result preserves all bits, including UXL, reserved bits, and arbitrary SPP/SPIE/SPELP/MPELP values. The public identity contracts intentionally use the full source MsFacts bundle; they do not claim the enabled-SIE case.

## Proof and event review

Read every pure proof body. The lower-view lemmas use bit extensionality over the actual generated field definitions. The generic `update_extract_self` handles arbitrary widths and slices; field identities instantiate it. Dirty-bit normalization uses the explicit source XS/FS/VS Off and SD=0 conjuncts, and nominal MPP is taken from MsFacts. No native bitvector decision procedure supplies these proofs.

The generic `legalize_plan` covers arbitrary old/new status words and all four raw MPP encodings. It constructs an owned MISA read node for each actual read after unfolding the generated legalizer and eager extension queries. MPP 0 and 1 retain their nominal values, 2 follows the actual lowest-supported-privilege User fallback, and 3 remains Machine. Eager virtual-memory alternatives and repeated S/U reads are retained; the one-cell footprint is a reusable ownership key, not a one-event trace claim.

The `off_plan` reduces the actual `legalize_sstatus` argument using the proved lift/mask identity and invokes that generic actual-program plan. No supplied evaluation-success, component-WP, or register-preservation premise is used. All registers remain unchanged. No mstatus, privilege, or MENVCFG cell is required by this isolated helper because status words are explicit arguments; the surrounding CSR execution must still perform and own its real reads/writes.

The `exampleStatus` definition resides with concrete proof certificates as a fixture helper. The coordinator explicitly accepted that placement; production definitions and the public contract remain separately located.

## Independent validation

- Fresh Link build passed: **351 jobs**.
- Fresh strict audit passed for **606 physical declarations across all six modules**, including private/generated declarations. Exporting was disabled, and dependency traversal included all types, opaque bodies via `allowOpaque := true`, and datatype constructors. All transitive axioms are among `propext`, `Classical.choice`, and `Quot.sound`; no unsafe/partial dependency or exclusion was accepted.
- Six new kernel theorem fixtures passed with an enforced foundational-axiom allowlist. They evaluate the actual generated legalizer using only a MISA snapshot, covering all four MPP values, the composed off program, missing-MISA rejection, nonzero saved ELP values supplied by the new word, zero saved ELP values supplied by a different new word, and the representative nonzero reserved/SUM/MIE/MPIE fields with UXL=3. The MPP-2 result is the corresponding User value; the other three remain unchanged.
- All six frozen implementation hashes match the owner manifest after review.

Evidence is retained under `/tmp/xv6-lean-research/`: `supervisor-sstatus-off-peer-build.log`, `SupervisorSstatusOffPeerAudit.lean`, `supervisor-sstatus-off-peer-audit.log`, `SupervisorSstatusOffPeerChecks.lean`, and `supervisor-sstatus-off-peer-checks.log`. The freeze manifest is `supervisor-sstatus-off-frozen.json`.

## Scope

This proves the exact already-disabled normalization and generic actual legalizer register plan. It does not prove the surrounding CSR permission path, destination-register assignment, enabled-SIE flip, instruction WP, full push_off, or any resource allocation. No new camera, memory event, reservation rule, or model assumption is introduced.

## Reviewed hashes

| File | SHA-256 |
| --- | --- |
| `SupervisorSstatusOffDefs.lean` | `ff881eae144f7272accb2522f1457ec1908737e172983214c164b46ecf197f82` |
| `SupervisorSstatusOffLink.lean` | `2d8106467e6c6ac96672c42fa4d7ca8f223992dc438a2bcaf4ebda6ee19ba3e2` |
| `SupervisorSstatusOffPlan.lean` | `fe46d5cffe6270663c0d1747213c49fbc87fecd2554673345f50d5d98227c606` |
| `SupervisorSstatusOffProofs.lean` | `4c3464deedb6209daaacc92436f881270049e8f556c0f25f05d2a4207217171e` |
| `SupervisorSstatusOffPure.lean` | `f23cbab66f5670059d267df3f33d7a413040f3de4e04b5548aaea701c4accfae` |
| `SupervisorSstatusOffSpec.lean` | `b553e9d7faa58d985f2d7972f6109e4d430ede7b819a92974f7e105557c6051a` |

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
