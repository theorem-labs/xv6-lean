# Sconf: frozen native source configuration component

All three pure and fourteen resource contracts are implemented, unchanged
from the coordinator-approved Defs/Spec. Four modules compile in893 jobs
(Proofs1.4s, Link1.0s). The strict owner audit checks all63 physical
declarations, including private/generated roots, with exporting disabled
and full types, opaque bodies (allowOpaque=true), and inductive constructors.
Only propext/Classical.choice/Quot.sound; no unsafe/partial dependency;
zero exclusions, no sorry/custom axiom/native_decide/bv_decide.

Source IntrDefs.v595–686 at paper pin
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476, constants RiscvFetchExec.v225/240,
and exact empty marker MinstretInv.v341. The body keeps every source
conjunct: native HardwareConfig, emp retirement marker, full Supervisor
privilege, actual msOwnAt, full mie0x220 and arbitrary sufficiently delegated
mideleg, full MENVCFG_S0xA000000000000000 plus all four environment facts.
There is no additional SIE pin, no fixed mideleg literal, and no invented
counter ownership in the emp marker.

The same MycpuRegimeShell capacity supplies hardware, typed registers and
SupervisorBits; runtime era names are unchanged. hardware_persistent unfolds
the exact existing HardwareConfig definitions and derives native persistence
from real discarded cells, static claims and the actual generation
certificate. It does not depend on the coordinator's simultaneously authored
HardwareConfig implementation, nor assume persistence or duplicate ownership.

Proof mapping:

- environment_literal uses ordinary kernel equalities for the four source
  bit facts and the literal; delegated_literal uses ordinary kernel decide.
- intro_config packages actual native cells and msOwnAt. open_parts and
  close_parts expose/reassemble the same body; no state execution is assumed.
- at_open matches source sconf_at_open: it removes the single msOwnAt and
  places all other resources inside a universally quantified replacement
  wand. at_close applies that wand to the actual held msOwnAt.
- at_facts projects the ten existing MsFacts. at_sret/at_sie use real
  SupervisorBits agreement with additional owned fragments.
- hardware_access duplicates only the persistent hardware assertion.
  interrupts_access and environment_access borrow full physical cells and
  capture their exact pure facts and all remaining ownership in reassembly
  wands; they do not assume arbitrary CSR updates preserve source constants.
- privilege/enable/environment agreement uses native dependent-register
  GhostMap agreement with a separately supplied actual cell.
- nativeSpec and existing48-slot registrySpec discharge every contract,
  without a component-spec premise, new camera or new world allocation.

Reproduction:

- PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.SconfLink
- PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/SconfOwnerAudit.lean

Evidence: /tmp/xv6-lean-research/sconf-build.log and sconf-owner-audit.log.
Final independent coordinator review remains pending.

This is the source configuration resource component, not full sie_cap_gpr,
CSR execution, enabled-handler correctness or boot resource inhabitation.
PC/counter/hart-state ownership, GPRs, translation slot/residue, timer and
stack resources remain separate source components for later composition.
No generated, umbrella, registry or other-owner source was edited.

Coordinator final peer review also passed: all implementation files read and
a fresh full audit checked 63 physical declarations through types, opaque
values and constructors, with standard axioms only and zero exclusions.
The corresponding peer report is in docs/reviews.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
