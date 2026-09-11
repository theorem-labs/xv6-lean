# Native shared-KPT leaf write event: frozen

Six modules implement both fields of the fixed, reviewed Spec. Defs/Spec
were authored by the coordinator; Slots/Update/Proofs/Link were implemented
by the Codex lean_logic_audit agent after independent interface/source
review. NativeSpec constructs all ownership and write-rule dependencies;
registrySpec uses the existing KptGhost registry, with no new slot.

`update` opens the invariant under any mask containing its namespace. The
snapshot agreement transports the supplied Maps path to the current tree,
retaining the exact upper raw words and leaf-slot address. Canonical equality
of the new word derives its actual two-bit A/D variant of the current leaf;
leaf validity is obtained from Maps. No owned slot, chosen current word,
update oracle, map lookup assumption or restoration callback is required
from the caller.

The full path accessor removes the actual three owned slots. The leaf's
original per-byte floors, bounds and all three publication-anchor arms are
retained via the existing SupervisorPteAD slot_open/slot_close laws.
TsoPinnedWriteWP.bundle_store consumes the same complete heap metadata and
TSO interpretation supplied for g and returns them for the exact writeState,
including physical-byte overlay, authored log append and unchanged outside
addresses. The slot family law restores the new leaf assertion with the
same allowed sets. The path is closed as setLeaf; its canonical snapshot,
full mapping authority, publication bound, and complete mapped/absent-VPN
TreeSpec are restored inside the same invariant.

`wp_write` is the actual dependent writeMem-8 event rule. It keeps every
request metadata field and distinguishes the event width from req.size;
its explicit guards are present payload, RAM address and exclusive access.
The existing native conditional rule derives held-snapshot readback from
the supplied reservation fragment. No successful response or reservation
disjointness is assumed. The rule's top-to-empty mask transition occurs
before its later. After that later it restores top, invokes the closed
shared update and supplies the genuine continuation. The invariant is never
held open across an event. Blocked retry retains the pre-state and payer;
success clears the reservation, advances the selected view to old log
length + 1, and returns the exact positive authored receipt at time - 1.

Source correspondence: HartSKpt.v:748–902, kpt_leaf_write_node;
PtTree.v:1148–1168, kpt_slot_pin; KptShare.v:86–150, shared body and snapshot;
and the previously proved pinned store and native conditional-write rules.
Source pin fa7f0a01c4b40489fac8ad303f079c2dfc7a1476, generated model pin
23dcf8fd923eb8a1958795393d2975632aa940b2. Unlike the source wrapper's particular
mk_pte family, the interface accepts a Maps leaf and canonical-equal new
word. The complete TreeSpec and proved generic set_leaf_spec discharge the
source mapping obligation internally. The modular offset helper already
proves the eight-byte store bridge, so no new global no-wrap premise is
introduced. A/D monotonicity is not asserted by this event rule.

This is the shared leaf write event and resource update, not an entire
translation or write_pte_conditional program WP. Shared exclusive re-read,
full A/D program composition, TLB-hit/refresh integration, publication from
boot and cross-prover semantics remain separate obligations.

Validation: complete target build passed 742 jobs; new Slots/Update/Proofs/
Link took approximately 0.9/1.2/1.2/0.8 seconds. The fresh audit checked all
18 physical-origin declarations across six modules, including types,
opaque theorem bodies and datatype constructors. Only propext,
Classical.choice and Quot.sound occur; no unsafe/partial semantic dependency
and zero exclusions. No sorry, custom axiom, native_decide or bv_decide.

Reproduce with `python3 tools/lake.py build Xv6.Kernel.KptWriteEventLink`.
Local audit and logs: /tmp/xv6-lean-research/KptWriteEventAudit.lean,
kpt-write-event-build.log, kpt-write-event-audit.log. Defs/Spec and all frozen
dependencies remain unchanged.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
