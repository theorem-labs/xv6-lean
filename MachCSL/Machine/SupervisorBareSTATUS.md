# Supervisor Bare translation

Implemented and frozen for independent review in `SupervisorBareDefs`,
`SupervisorBareProofs`, and `SupervisorBarePlan`.

`mode_plan` proves actual `translationMode Supervisor` returns Bare from
`mstatus.SXL=2` and `satp.Mode=0`. It performs exactly the actual mstatus and satp
reads, including the pure RV64 assertion and mode decoding. Its generic partial
footprint requires only those two fractional cells.

`translate_plan` proves actual `translateAddr (Virtaddr address) access` returns
`Ok (Physaddr address, PBMT_PMA, ())` with the register file unchanged. Its
three-cell footprint is mstatus, current privilege, and satp, at independently
supplied fractions. The actual sequence is four reads: mstatus, current
privilege, mstatus again, then satp. The supporting privilege and non-shadow
lemmas derive the actual computations; they are not caller-provided execution
or translation-correctness assumptions.

The supported family exactly follows pinned `SRegime.v:182–185`, `s_acc_ok`:
instruction fetch, ordinary data load/store, and AMOSWAP with arbitrary acquire
and release flags. `Config` requires current privilege Supervisor, SXL=2, and
Bare satp mode. `Effective` requires either instruction fetch or MPRV=0.
`fetch_plan` imposes no MPRV/MPP restriction; `mprv_zero_plan` packages the
source's usual kernel data-access condition. No misa.S premise or read is
needed by this generated branch. ASID, PPN, TLB, address bits and all unrelated
register fields remain arbitrary. There is no canonical-Sv39-address premise.

Source mapping at xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`:

| Lean boundary | Source / generated definition |
| --- | --- |
| `Supported` | `SRegime.v:182–185`, `s_acc_ok` |
| `mode_plan` | `SRegime.v:66–90`, `exec_translationMode_S_bare`; actual `Vmem.lean:426–445` and `SysRegs.lean:1082ff` |
| `translate_plan` | `SRegime.v:96–121`, `exec_translateAddr_bare`; actual `Vmem.lean:556ff` |
| `effective_supervisor`, `not_shadow` | Actual `SysControl.lean:222ff` and `VmemTypes.lean:279ff`; source fetch/MPRV-zero privilege reductions |
| Three-cell footprint | Registers actually used in that source Bare reduction; `bare_inv` itself at `SRegime.v:833–837` additionally owns the separate PMP configuration |

The source `bare_inv` explicitly owns no TLB. This slice does not reconstruct
the entire invariant or consume its PMP resources: translation in Bare mode
performs no PMP or RAM access, so those caller resources remain framed.
`footprint_unique` supplies native `RegisterPlan.fold`'s uniqueness premise.
Folding the plan with the existing generation certificate, those exact cells,
and a continuation gives the corresponding real terminal native WP without a
new camera or additional preservation oracle. No separate native wrapper was
required for this slice.

Pointer masking and `transform_effective_address` are separate, even when
satp is Bare. This proves neither those data wrappers, actual memory accesses,
full instruction fetch, the KPT branch, `strans_inv`, nor the complete mycpu
specification. In particular, it does not identify KT0 with Bare or assume that
the source's nonidentity KT1 stack mapping is an identity mapping.

Validation:

- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Machine.SupervisorBarePlan`
  passed 426 jobs; final plan module approximately 889 ms.
- `/tmp/xv6-lean-research/SupervisorBareAudit.lean` checked all 55 physical-origin
  logical declarations in all three files, including private helpers, generated
  declarations, and full type/opaque-body/constructor dependency cones.
  Only `propext`, `Classical.choice`, and `Quot.sound` occur. Zero unsafe/partial
  semantic dependencies and zero excluded runtime companions. Audit output:
  `supervisor-bare-audit.log`; build output: `supervisor-bare-build.log`.
- No `sorry`, custom axiom, `native_decide`, `bv_decide`, semantics alteration,
  new camera slot, or edit outside the owned prefix.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
