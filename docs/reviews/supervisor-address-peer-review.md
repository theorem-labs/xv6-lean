# Supervisor address transformation independent review

Reviewer: OpenAI Codex subagent `/root/lean_logic_audit`, independent of the
coordinator author. **PASS** for the declared mode-parametric address-only
scope; no requested correction.

Read all five frozen SupervisorAddress modules and design, compared pinned
xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`
`HartSMem.v:375–430,484–550`, and inspected actual generated
`PmUtils.lean:210–257`, `Vmem.lean:426–447`, and
`VmemUtils.transform_effective_address`. The implementation proves the Data
load/store specialization of the source identity transform, with concrete
configuration facts replacing the source's abstract effective-privilege fact.

Exactly four independently fractional register cells support all six reads:
mstatus, current privilege, mstatus again for pointer-mask applicability,
menvcfg, mstatus again for architecture, then satp. The explicit MXR-zero
condition ensures the actual Supervisor PMM applicability path; disabled PMM
is decoded from the actual menvcfg field. The SXL/decoded-mode conditions
justify the real architecture and satp processing. No invalid-mode/error path
is dropped through an assumed effectful contract.

The mode remains arbitrary among decoded SATP modes. Both `physical_zero`
and `virtual_zero` prove exact 64-bit extraction/extension identities before
`program_plan` branches on Bare. No address canonicality, truncation, fixed
reset register file, ignored eager read or whole-register ownership appears.
All other register fields remain arbitrary. The plan constructs unchanged
register-file returns, and the native fold restores the same four cells to
its continuation with ordinary generation handling. It allocates no camera,
requires no memory resource or software WP oracle, and claims no memory
translation/access, base-register address formation or function correctness.

Independent rebuild passed **457 jobs**. Fresh physical-origin audit covers
all **81 declarations in five modules**, including private helpers and
transitive types, opaque bodies (`allowOpaque := true`) and constructors.
Only `propext`, `Classical.choice`, `Quot.sound`; no unsafe/partial logical
dependency, zero excluded runtime companions. Evidence:
`/tmp/xv6-lean-research/SupervisorAddressPeerAudit.lean`,
`supervisor-address-peer-audit.log`, `supervisor-address-peer-build.log`.
No production file was changed. Whole generated-model/Rocq correspondence
remains separate from this native proof review.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
