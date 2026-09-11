# Static identity map and native claim allocation

The coordinator read the complete KMap.v and the relevant classifier,
identity arithmetic and map-construction section of KptPt.v at paper pin
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. This component instantiates the
already-native KptGhost map with the exact source initial static map.

The classifier gives RX to VPNs [0x80000,0x80007), RW to
[0x80007,0x88000) and [0xc000,0x10002), and no entry elsewhere. Each PPN
is the same VPN zero-extended to 44 bits. The device interval intentionally
retains the source's complete range, including gaps between actual devices.
There are 49,154 entries; no consumer should normalize the whole map.

The Lean representation uses increasing interval insertions and disjoint
ExtTreeMap unions. The source uses an association list converted to a gmap.
Exact lookup equivalence, including absent keys, is the public contract
that justifies this representation difference. The initial-map definition
is irreducible to ordinary elaboration; only its own lookup proof unfolds it.

Seven pure contracts give interval lookup, total initial-map lookup, exact
classifier cases and bound, positive-address identity reconstruction and
text/data address classification. Five native contracts give persistence,
authority timelessness, allocation from the existing actual GhostMap,
static-fragment extraction and exact-authority identification. Allocation
returns a fresh actual name, its full authority, all persistent static claims
and the supplied frame. It does not claim allocation at an existing era name.

The capacity, map camera and resource assertions are the already reviewed
KptGhost ones, with the same discarded claims. No physical tree or
translation fact is invented. Dynamic map insertion, physical table-building,
boot publication and installation into the complete hardware configuration
remain consumers. The complete source sconf/hw_config requires this bundle;
its other native register and generation resources remain separate.

The signature checkpoint passed 410 jobs and independent review. All twelve
contracts are now implemented; the full build passed 655 jobs. Coordinator
and independent peer audits each checked all 79 physical declarations and
their full dependency cones, with the standard three axioms only, no unsafe
or partial dependencies and zero exclusions. Ghost-only recursive map
construction is noncomputable, avoiding an unnecessary runtime companion.
No existing module or umbrella is changed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
