# Disabled supervisor capability: frozen native component

All nineteen approved resource contracts are implemented in four modules.
Full build917 jobs (Proofs1.2s, Link828ms); strict owner audit covers all67
physical declarations, exporting disabled, full types/opaque bodies
(allowOpaque=true)/constructors, standard three axioms only, no unsafe or
partial dependencies, zero exclusions. No sorry/custom axiom/native_decide
or bv_decide. Native and existing48-slot registry Specs have no supplied
component-law premises.

Source IntrDefs.v1968–2062,2660–2950,3184–3276,3358–3420,3470–3560;
trap_res at573, SRegime.v1750–1792; paper pin
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. The b=false specialization keeps
all six conjuncts: actual context-owned virtual stack, real source translation
slot, disabled ghost eighth, actual running context, same-hart timer capability
and the source tier witness. The unused disabled-arm process pointer is omitted.
The tier witness is emp at identity and actual kptOn at full, independently
of SIE. Identity/RW/RAM claims remain in the actual stack words; no pure
Admits predicate replaces the receipt. The GPR package adds full active
hart-state, complete Sconf and full native HartTp.pinnedFile.

Proof mapping:

- witness_identity/receipt/persistent match source sr_ktier_wit. The real
  kptOn is required for tier_up; native stack weakening alone cannot fund it.
- intro_cap/open_cap retain the exact six-conjunct bundle. intro_bare consumes
  actual pending/Bare/stvec resources through SupervisorTranslation's native
  constructor and costs no fabricated TLB or full-tier witness.
- timer_access and witness_access duplicate only persistent resources.
- retarget/push/pop/grow/shrink reuse native KernelStack split/append laws;
  all original source modular addresses and arithmetic premises remain.
  The exact non-stack remainder is framed, including the linear running
  context, off token and translation slot.
- two_words borrows the two real KernelDatum words while capturing the actual
  deeper stack/remainder. New word contents may close because source stack
  contents are existential; there is no copied word or restoration oracle.
- gpr_intro/open preserve actual native hart/config/file cells. gpr_at_open/
  close use the actual Sconf replacement accessor without duplicating its body.

Reproduction:

- PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.SieOffCapabilityLink
- PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/SieOffCapabilityOwnerAudit.lean

Evidence: /tmp/xv6-lean-research/sie-off-capability-build.log and
sie-off-capability-owner-audit.log. Final coordinator review is pending.

No enabled handler, CSR/SIE transition, scheduler migration, boot resource
inhabitation or whole function WP is claimed. Every prerequisite was already
native; no new camera, registry identity, generated or other-owner source
was changed. See docs/design/sie-off-capability-boundary.md.

Coordinator final peer review also passed: all implementation files read and
a fresh full audit checked 67 physical declarations through types, opaque
values and constructors, with standard axioms only and zero exclusions.
The corresponding peer report is in docs/reviews.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
