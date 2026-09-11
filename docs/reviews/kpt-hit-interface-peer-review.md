# Shared KPT hit interface: independent review

PASS for the frozen interfaces in `Xv6/Kernel/KptHitDefs.lean` and `KptHitSpec.lean`. This reviews the statement and its source correspondence; it does not claim an implementation of `Spec` was checked. The coordinator authored these interfaces. The reviewing Codex agent separately implemented some of their previously reviewed ownership and exclusive-read dependencies.

The comparison used the pinned artifact `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, especially `HartSTrans.v`'s `swp_translate_hit_ex` and the kernel specialization in `HartSKpt.v`, together with actual generated `LeanPaperStock/Vmem.lean:448–472` and the existing `KptAD`, `Sv39Hit`, and `TlbCoherence` contracts.

The resident entry premise describes the actual indexed TLB entry, including raw upper pointers, accumulated global bits, and leaf origin address. Canonical snapshot mapping and coherence permit stale A/D bits without assuming a successful physical read. The six-cell bundle consists of the five A/D control cells and the TLB cell. Shared clients, reservation ownership, and returned coherence remain explicit.

The four branches retain their precise guards: cached and disabled require zero, reread requires one, and written requires two. Branch facts occur inside those guards. Reread returns the actual snapshot reservation and view receipt; successful conditional write returns its actual log receipt and cleared reservation. Only an `Ok (some updatedWord, ...)` A/D response refreshes the TLB. The successful translation returns PPN and PBMT from the original entry, as the generated program does, rather than silently substituting the refreshed entry.

The uniform A/D `Config` premise is stronger than an isolated cached or disabled branch needs, but supports the same public contract when the actual enabled path must execute. Arbitrary ASID is a valid generalization of the source kernel's ASID-zero specialization. This interface covers the actual hit program after residency has been established; it does not establish the preceding lookup, SATP selection, or full translation operation. No blocking issue or statement correction was found.

Independent validation: the target build passed (442 jobs). `/tmp/xv6-lean-research/KptHitInterfacePeerAudit.lean` checked all 21 physical declarations in the two modules, with zero exclusions, traversing declaration types, opaque bodies (`allowOpaque := true`), and inductive constructors. The full dependency cones use only `propext`, `Classical.choice`, and `Quot.sound`, with no unsafe or partial dependency. Evidence is in `kpt-hit-interface-peer-build.log` and `kpt-hit-interface-peer-audit.log` under the same research directory.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
