# Combined boot export: frozen native component

All three approved contracts are implemented in four modules. Full build:
884 jobs; Proofs and Link 1.2 seconds each. Strict owner audit checked all
18 physical declarations, including private/generated origins, using
exporting=false and full types, opaque bodies (allowOpaque=true) and
constructors. Standard three axioms only, no unsafe/partial dependency,
zero exclusions. No sorry/custom axiom/native_decide/bv_decide. nativeSpec
and registrySpec discharge all component premises.

produce preserves the actual Era.interp, full static-map authority,
persistent static claims and both physical and identity text, while
consuming the retained eight full PMA register cells through
BootPma.nativeSpec. It returns their persistent discarded pmaBoot cells
and the exact textRetained resources: 179 remaining registers per hart,
exact sparse byte/timestamp remainder, log-length receipt, all metadata,
devices, durable disk and reservations. A private generic frame prevents
proofmode from expanding the large concrete static-map predicate; its
public instantiation is exactly the actual native five-column prefix.

allocate_frame calls KernelTextBootMap.nativeSpec.allocate_frame once.
The actual returned era and boot facts instantiate produce. The Installed
fact and literal caller frame are returned unchanged. allocate specializes
this genuine allocation to emp. There is no second era allocation or text
carve, no duplicated linear ownership, no supplied authority, installed
name equality or resource correctness oracle. encodeAll stays symbolic.

Source mapping is inherited explicitly: ArchReset.v:245–276 actual board
PMA and generated reset, BootCarve text persistence, source sparse code
map and native static-map installation in the actual era name. Source pin
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. This combined export establishes
no S-mode state, source supervisor capability, physical KPT, translation
token or full native function-entry resource inhabitation.

Reproduction:

- PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.BootTextPmaMapLink
- PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/BootTextPmaMapOwnerAudit.lean

Evidence: /tmp/xv6-lean-research/boot-text-pma-map-{build,owner-audit}.log;
exact source hashes/lengths in boot-text-pma-map-frozen.json. Design:
docs/design/boot-text-pma-map-boundary.md. Final independent coordinator
review passed all four modules and an independent 18-declaration strict audit;
see docs/reviews/boot-text-pma-map-peer-review.md. No previous owner file, generated semantics, registry slot
or umbrella was modified.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
