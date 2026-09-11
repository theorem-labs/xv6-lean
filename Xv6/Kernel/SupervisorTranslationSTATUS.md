# Supervisor translation slot: frozen native component

All eighteen approved contracts are implemented in four modules, with
nativeSpec and the existing48-slot registrySpec closed. Build670 jobs;
Proofs1.0s and Link834ms. Strict independent owner audit covers all60
physical declarations, including private/generated declaration roots, with
exporting disabled and complete type/opaque-body/constructor traversal.
Only propext/Classical.choice/Quot.sound occur; no unsafe/partial dependency;
zero exclusions. No sorry, native_decide, bv_decide or custom axiom.

Source: RiscvPtsto.v591–596, IntrDefs.v807–916/1178–1268, and
SRegime.v352–353/833–837, pinfa7f0a01c4b40489fac8ad303f079c2dfc7a1476.
The exact source bare_inv includes full SATP/ModeBare and both full PMP
vector cells through the existing source PMP predicate. The Bare slot owns
stvec and one pending half; the KPT arm owns full shot and the complete
existential-root residue (including actual TLB), with no stvec. The slot is
linear; its KPT residue contains the existing native shared invariant.

The existing machine view capacity supplies mono-nat slot3; runtime names
are explicitly era.supervisorTranslation cpu. No new camera, registry entry,
InvGS allocation or authority assumption was added. Fresh allocation returns
an existential name, optionally satisfying a cofinal freshness predicate;
it does not claim to allocate a resource at a preselected existing era name.

Proof mapping:

- Four native Timeless/Persistent instances correspond to source §6b.
- halves is native mono-nat fractional equivalence at0; allocate/allocate_fresh
  use genuine native fresh ownership allocation and split full authority.
- flip consumes both halves and applies monotone update0→1, returning full
  authority and persistent lower-bound1. receipt uses native lower-bound mint.
- on_pending_false uses actual authoritative lower-bound validity;
  pending_shot_false uses authoritative value agreement0≠1 (the source uses
  the simultaneous invalid-fraction fact); shot_exclusive uses native full
  authority exclusivity. These are resource contradictions, not assertions
  about physical CSR state inferred from a token alone.
- bare_intro/access are exact resource assembly/opening. intro_bare/intro_kpt
  choose the two source arms. access_bare refutes the KPT arm and returns
  both pending halves and exact Bare/stvec resources. access_kpt refutes the
  Bare arm, borrows the actual residue and captures shot in its reassembly
  wand. The persistent on receipt can remain with the client.

Reproduction:

- PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.SupervisorTranslationLink
- PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/SupervisorTranslationOwnerAudit.lean

Evidence: supervisor-translation-build.log and
supervisor-translation-owner-audit.log under /tmp/xv6-lean-research.
Independent coordinator review of final proofs remains pending.

The source's larger strans_res_at/swp/derived s_regime interface,
operational CSR/SATP/TLB installation, boot allocation of all per-era names
and complete supervisor-capability inhabitation remain separate. Flip alone
neither switches hardware nor publishes physical page tables. The approved
Defs/Spec signatures were retained unchanged throughout implementation.

Coordinator final peer review also passed: all implementation files read and
a fresh full audit checked 60 physical declarations through types, opaque
values and constructors, with standard axioms only and zero exclusions.
The corresponding peer report is in docs/reviews.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
