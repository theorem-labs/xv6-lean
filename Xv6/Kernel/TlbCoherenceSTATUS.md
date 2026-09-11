# Pure TLB coherence and actual register plans: frozen

All six modules compile successfully (449 jobs). Link constructs
`nativeSpec` with all twenty pure contracts and `nativePlanSpec` with all
four actual register plans. The owner audit checks all 101
physical-origin declarations and their complete type, opaque-body and
constructor dependencies: only `propext`, `Classical.choice`, `Quot.sound`;
no unsafe/partial dependency and zero exclusions. No custom axiom or native
decision tactic is used.

The exact single-tree source CacheOf/Coherent relation permits foreign VPN
tags with equal hashes and covers all 64 physical slots. It preserves exact
ASID/global/level-mask/origin-address fields and arbitrary stale A/D bits.
Stored ASID is fixed while request ASIDs remain arbitrary in actual tag
and lookup laws. Cached validity is a derived conclusion, not a premise.
Canonical tree transport preserves cache provenance; source A/D-only leaf
updates preserve the full vector without requiring redundant classification
premises. Matching actual tags recovers the query's complete Maps path;
a blocked VPN cannot produce a hit, including through a hash collision.

Actual lookup uses one TLB read. Fill reuses the frozen generated plan and
retains the read, write and final universally quantified callback read.
PTE refresh uses the actual one-read/one-write write_TLB, preserving all
other entry fields. PBMT extraction follows its real Sail program. The
bounded getter loop is proved through the generated IntRange equations.
The Plan footprint is one full TLB cell; no other register snapshot is
assumed.

Source definitions and laws: PtTree.v:1693–1791,1954–1991;
CommonWalk.v:795–806; actual getter/tag/blocked-query closure at
PtTree.v:2174–2541; shared snapshot scope KptShare.v:153–220. Source pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, generated model pin
`23dcf8fd923eb8a1958795393d2975632aa940b2`.

This is a pure provenance layer and four actual register plans. It does
not provide physical ownership, a shared-invariant accessor, full
translate_TLB_hit WP, SATP-switch/two-tree coherence, or cross-prover model
equivalence. Those remain explicit separate obligations. No successful
translation, read, permission check, or A/D update is assumed. No new
camera is introduced. Full design is in
`docs/design/tlb-coherence-boundary.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
