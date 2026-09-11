# Independent disabled mycpu adapter review

PASS for the six-module disabled Bare adapter. The coordinator read all
module contents and compared the boundary with SpecMycpu, ProofMycpu,
IntrDefs' msOwn/off arm/sie_cap_gpr, and the previously reviewed HartTp
representation. The native Link discharges both capability and function
specifications using the same physical register capacity.

The reversible partition consumes 21 control cells, one full mstatus and
31 full GPRs, and produces exactly 28 cycle cells, eleven saved cells and
fourteen explicitly framed cells. The x0 fact is retained. SIE follows from
actual tied-fragment agreement; MPRV/MXR/SXL follow from MsFacts. Physical
TP comes from the full pinned x4 cell, not from a persistent pure ghost.

The actual fourteen-cycle theorem supplies the result. The returned software
map changes only x10 and x15. Reassembly uses owned RA/saved/TP equality for
the seventeen GPRs present in the function theorem, and the original cells
for the fourteen others. It never projects an arbitrary unowned returned
register. The same mstatus restores all original bit fragments and the
off-token without updates. The continuation receives all 53 physical cells,
code/context/stack resources and the cleared reservation, for every next
clock choice.

The software saved-value result alone is a definitional map-update fact;
its physical meaning is furnished by the separately checked resource
reassembly and the native function result. The adapter accurately leaves
Bare hardware assumptions and physical stack ownership explicit. It does
not claim the source's complete sie_cap_gpr, KPT tiers, free-stack conversion,
interrupt migration or preceding call instruction.

The owner build passed 892 jobs. The coordinator independently reran the
full audit over all 202 declarations, following types, opaque bodies and
constructors: standard three axioms only, zero exclusions, and no
unsafe/partial semantic dependency. Evidence:
/tmp/xv6-lean-research/MycpuOffAudit.lean and mycpu-off-root-audit.log.

This review used distinct implementation and review AI-agent roles; it is
not a human review.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
