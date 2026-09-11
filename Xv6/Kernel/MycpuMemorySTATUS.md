# Four actual mycpu memory bodies

Frozen: MycpuMemory{Defs,Spec,Plan,Proofs,Link}. Native `wp_store`, `wp_load`
and constructed `nativeSpec` cover actual compressed indices 1/2/10/11 via
execute/ExecuteAs and the real STORE/LOAD bodies. Source mapping:

| Index / offset | Body | Physical/Bare word |
| --- | --- | --- |
| 1 / +0x02 | C_SDSP RA,8(SP) → STORE | SP+8 receives actual RA |
| 2 / +0x04 | C_SDSP S0,0(SP) → STORE | SP receives actual S0 |
| 10 / +0x18 | C_LDSP RA,8(SP) → LOAD | RA receives word at SP+8 |
| 11 / +0x1a | C_LDSP S0,0(SP) → LOAD | S0 receives word at SP |

The certified MycpuDecode instructions and normalized bodies are used directly.
The store reads its source before SP; ext_data_get_addr forms the exact modular
sum; the real pointer transformation, virtual-memory wrappers, alignment/page
split, permission checks and memory event are retained. All 29 register reads
precede a store event; a load has 22 reads, then the real read event and target
write. No destination read is invented. STORE ignores the returned Boolean,
so its false-write tail also retires; the pure boundary proves this exact
behavior. LOAD keeps all word/tag tails and error Exit, with the genuine
full-width extension and destination write following successful memory access.

The one ten-cell footprint contains eight independently fractional configuration
cells (mstatus, privilege, menvcfg, satp, PMA, PMP configuration, PMP address,
HTIF), fractional SP and the selected data register. A store uses the selected
fraction; a load requires full target ownership. The concrete memory boundary
is widened to these ten cells and folded directly. The native load suffix then
uses RegisterPlan.fold to restore the updated full footprint. No shared
configuration cell is duplicated or reallocated. Unlisted registers need no
ownership assertion.

`ReadConfig`/`WriteConfig` expose actual Supervisor/SXL2/Bare/MPRV-clear,
MXR-clear/PMM-disabled address transformation, TOR RAM, disabled HTIF and the
relevant matched readable/writable PMA. All other register values, input words
and platform predicates are arbitrary. Native alignment is derived from the
actual context-word resource. `wp_store` retains the existing blocked retry
with old word/reservation, then yields the new authored word, cleared
reservation and unchanged ordinary-view receipt. `wp_load` preserves the
fractional word/context and reservation, returns the selected-view receipt,
and updates only the target in its register package. Full heap metadata/TSO
bookkeeping comes from the existing context memory rules. Both return through
a genuine guarded final continuation; no software/access/translation oracle
is a public premise.

`after_value`, `after_sp`, `after_PC`, `after_nextPC` and `after_address` prove
exact target-update projections. `pushed_ra_address` and `pushed_s0_address`
identify the two source save slots after the modular sixteen-byte SP push,
for arbitrary entry SP, without a global no-wrap bound. Existing physical
stack split/join can frame the other word and arbitrary remainder; this slice
does not allocate or claim virtual stack ownership.

Source pin xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`:
ProofMycpu.v:99–136,212–248 and WpSconfMem.v:3656–3741. Generated source paths
are listed in docs/design/mycpu-memory-bodies-boundary.md. The source's
virtual/tier word, SIE capability, fetched instruction and retirement contracts
are stronger than this explicit physical/Bare prerequisite. This does not
prove the whole mycpu function, its actual Sv39/KPT stack regime, fetch/cycle,
trap migration, or source wp_next. Whole-model Rocq/Lean correspondence remains
separate. PC/nextPC pure projections describe the body, not retirement.

Validation: `python3 tools/lake.py build Xv6.Kernel.MycpuMemoryLink` passed
**627 jobs** (final Plan 1.5 s, Proofs 997 ms, Link 897 ms). Fresh physical-origin
audit checks all **135 declarations in five modules**, including private
helpers, transitive opaque bodies (`allowOpaque := true`), types and inductive
constructors. Only `propext`, `Classical.choice`, `Quot.sound`; no unsafe/partial
logical dependency and zero excluded runtime companions. No sorry, custom
axiom or native decision tactic. Evidence:
`/tmp/xv6-lean-research/MycpuMemoryAudit.lean`, `mycpu-memory-audit.log`,
`mycpu-memory-build.log`. No frozen dependency file was edited.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
