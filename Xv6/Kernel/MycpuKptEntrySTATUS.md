# Full-tier source entry adapter: frozen native component

All four pure and four native approved contracts are implemented in five
modules. Full build966 jobs (Pure1.1s, Proofs1.3s, Link1.0s). Strict owner audit
checked all53 physical declarations, including private/generated origins,
with exporting disabled and full types/opaque bodies (allowOpaque=true)/
constructors. Standard three axioms only, no unsafe/partial dependencies,
zero exclusions. No sorry/custom axiom/native_decide/bv_decide. Generic
nativeSpec and existing48-slot registrySpec discharge all component fields.

Source mapping: complete ProofMycpu.v, StackOwn.v151–225 and its two-slot
introduction/elimination laws, plus the exact source components already
ported in SieOffCapability/SieOffPacket. Paper pin:
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. This adapter prepares and restores
resources for the actual native body/cycle packet; it proves no instruction
or whole-function WP and does not replace the actual prologue/epilogue.

The input is full-tier source capability+pc_is at mycpu's first address,
with an explicitly supplied actual same-hart discarded pmaBoot cell and
separately supplied MycpuKptFetch.code. Code is neither allocated nor
inferred from image bytes here. Native packet opening derives Ambient and
Admits; the actual full-tier receipt eliminates the Bare slot. The actual
root and source kptN are preserved. Register agreement pays the boot-table
equality needed by current execution configurations, and the original
extra fragment is retained. General source Sconf/PmaClass is unchanged.

config derives the exact native Cycle.Config from those paid facts. Its
ELP proof uses the actual one-bit zero/one dichotomy and not-LP_EXPECTED;
no stronger arbitrary status constant is imposed. The existing full MISA,
MENVCFG literal, delegation, active/Supervisor and HTIF facts supply the
remaining fields.

save_area reuses native KernelStack.frame_two. RA slot=entrySP−8 and S0
slot=entrySP−16 by checked modular bitvector equations. Both initial words
are arbitrary actual stack contents. The exact tail remains anchored at
entrySP−16 with depth available−2. No extra stack alignment, range,
disjointness or known pre-store saved-value assumption is introduced.

resources exposes the actual50-cell source packet, code, running context,
immutable-entrySP word pair, actual existential reservation and literal
frame. The frame retains the tail, timer, tier receipt, whole hardware,
linear shot and PMA fragment. It hides neither a resource callback nor a
running context. The function proof may pass this exact frame through its
native cycles.

close_entry consumes the actual returned pair/packet/frame, with available≥2,
returned file SP=entrySP and owned-projection Boundary(returnPC). The pair
may contain arbitrary returned values: source stack contents are existential.
The native stack equivalence restores the entire available count and exact
source capability/pc_is, while returning code and the extra PMA fragment.
It assumes no callee-saved result, register result, execution success or
clock trace; the later function proof must establish its actual return
boundary and SP restoration. certificate extracts the existing real
native generation certificate while retaining the full resources.

Reproduction:

- PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.MycpuKptEntryLink
- PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/MycpuKptEntryOwnerAudit.lean

Evidence: /tmp/xv6-lean-research/mycpu-kpt-entry-{build,owner-audit}.log;
exact hashes in mycpu-kpt-entry-frozen.json. Coordinator final independent
review is pending. See docs/design/mycpu-kpt-entry-boundary.md.

No existing module, generated model, registry slot or umbrella was changed.
Full14-cycle source function composition, kernel-text production and native
boot/resource inhabitation remain separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
