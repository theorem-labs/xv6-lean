# Kernel leaf permission and validation boundary

Owner: Codex coordinator. Source KptPt428–454/706–795 and Pt4kWalk26;
actual pinned generated VmemPte invalid/permission checks and Vmem check_leaf_pte.

The two permission classes are precisely RX and RW, with base bytes 0x0b and
0x07 and arbitrary accessed/dirty bits. The leaf word is the source concatenation
of a symbolic44-bit PPN and ten flag bits, zero-extended to64. WordSpec requires
actual generated flag/PPN/extension extraction, leaf classification, exact A/D
replacement and canonical equality. No concrete physical PPN is selected.

PlanSpec supports exactly instruction fetch, Data load, Data store and Data
AMOSWAP with arbitrary aq/rl. Allows permits fetch only RX, both loads and only
RW stores/swaps. For these cases, the actual permission program equals pure
success for arbitrary MXR/SUM. A store to RX is not admitted.

The invalid and complete level0 Sv39 leaf validators use RegisterPlan.Returns
on the actual generated Sail trees. Their footprints are empty because every
eager MISA/menvcfg read is proved harmless for every possible result. The reads
remain real events; no program=pure equality or erased source interpreter is
claimed for these validators. Extension bits are zero; level0 requires no
superpage alignment; the generated Svnapot and PBMTE reads still occur. The
actual successful result is the original PPN, PBMT_PMA and unit context.

These are finite native register plans, usable by the existing RegisterPlan WP
fold without whole-register ownership. No physical memory is read here. Actual
PTE reads, exclusive A/D rereads and conditional writes use the separately proved
native wrapper rules. Shared KPT ownership, three-level walk, TLB insertion and
the source supervisor invariant remain subsequent obligations. Defs/Spec are
reviewed separately before implementation and a final independent full audit
is required before publication.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
