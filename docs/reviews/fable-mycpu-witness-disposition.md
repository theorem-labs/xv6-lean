# Disposition of Fable eighth review

Fable approves the concrete witness and native Off/HartTp/SupervisorBits
adapter with no soundness blocker. Its source-only review covered122 frozen
files. The independent nine-module implementation review and full165-root
audit are recorded separately in mycpu-bare-witness-peer-review.md.

Both requirements for accurate closure wording are addressed:

- The original pool theorem has one thread. The new, separately reviewed
  MycpuBareWitnessPoolProofs.full_pool_positive proves positive execution in
  the actual twelve-thread pool, exactly power :: powerFork0 at both ends.
  It uses the same configured state, same fourteen-cycle derivation and same
  final full-machine record. All eight harts, all three device workers and
  power are present; only CPU3 is scheduled. The original nine proof modules
  are unchanged. full_pool_length checks the count, and the new module's
  five declarations passed full independent type/opaque/constructor audit.
- The witness fixes one concrete Platform instance (both reservation
  predicates false), Devices.initial, false optional-clock choices and reads
  at the minimal allowed view. configured is an explicit synthetic supervisor
  state with zero register files on the seven other harts. The total cache
  equals the complete actual loaded boot image. This is not boot reachability.

The narrow milestone is now closed: native Bare mycpu CPS plus a concrete
fourteen-cycle operational witness on the pinned image, reaching the same
exported Result/HartResult in the full thread pool. Native resource
inhabitation remains open: installation of era-named interrupt bits,
running-context ownership, supervisor register cells and the stack resources.
The full source KPT/SIE capability, virtual free stack, JAL-call wrapper,
all six whole-xv6 roots and cross-prover correspondence remain open. The
existential witness fixes its permitted choices; the general CPS admits
all clock successors.

The Off STATUS now explains that Result.saved and Result.ra on returnedMap
are bookkeeping. Their physical justification comes from body.saved,
body.ra and body.stable through returned_agrees and resource reassembly.
The new entry_ms_facts proves all ten source MsFacts for the witness's
actual mstatus, without asserting allocation of any bit ownership.

Fable listed base definitions absent from its packet. Those remain evidence
gaps in that source review, not claimed reviewed by Claude. Coordinator and
peer audits traverse their complete logical dependency cones, and the
actual pool, image and evaluator bridges have separate source/proof reviews.
The post-review full-pool addition was independently reviewed by the
coordinator; it was not part of Fable's frozen packet.

Next: shared translation through the existing page-table event rules and
both TLB paths; a regime-parametric cycle chain; era-named bit installation;
and actual call/interrupt-control code. Fable's suggestions do not substitute
for these implementations or close their boot obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
