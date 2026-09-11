# Actual Bare ordinary virtual store

Frozen: SupervisorBareWrite{Defs,Spec,Plan,Proofs,Link} and the shared
SupervisorBareWriteGeometry. `virtual_boundary` proves the actual generated
`vmem_write_addr (Virtaddr address) 8 word (Store Data) false false false` has
its complete register prefix followed by the real present-payload write.
`wp_write` and constructed `nativeSpec` derive its native WP from actual
context and full old-word ownership, generation certificate and reservation.
No translation, memory-access or successful execution callback is assumed.

One seven-cell footprint owns mstatus, current privilege, satp, PMA regions,
PMP configuration, PMP addresses and HTIF base at independent fractions.
All 21 actual register reads remain: initial effective privilege and translation
mode (four), translateAddr (four), mem_write_ea (six), and mem_write_value
(seven). The shared cells are used sequentially; no ownership is duplicated.
The actual singleton split, permission announcement, whole-word extraction,
value-write wrapper and Boolean result handling are preserved. `OneWrite`
retains both actual success and false-write tails. The native RAM rule proves
success, retaining exact blocked retry with old word/reservation until it
occurs, then giving the new word, cleared reservation and same-view receipt.
Full heap metadata, authored log append, TSO/context updates and generation
handling are discharged by the existing native context-write rule.

`Config` requires actual Supervisor privilege, SXL=2, Bare satp mode,
MPRV=0, TOR RAM grant, width-eight RAM interval, disabled HTIF, and a matched
writable PMA region. Other register values and both platform predicates are
arbitrary. Public native WP alignment is derived from full word ownership.
`split_page_eight` proves eight-byte alignment suffices for the actual page
split on modular 64-bit addresses; it adds no global no-wrap assumption.
The pure boundary exposes alignment explicitly because it has no Iris word.

Source: xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`,
`HartSMem.v:3098–3253`, including separate announcement/value stages at
3229–3245; generated `VmemUtils.lean:344–426`, actual Bare translation in
`Vmem.lean:556–593`, and `SplitAccessUtils.lean:276` onward. The native
contract specializes width-eight ordinary Data stores with concrete Bare
translation. It does not claim source KPT translation, address formation or
pointer transformation, full `vmem_write`, a STORE instruction WP, source
virtual stack ownership, or an entire kernel function. Conditional PTE writes
and other access/flag branches remain separate. Whole-model Rocq/Lean
correspondence remains a separate project obligation.

Validation: `python3 tools/lake.py build MachCSL.Logic.SupervisorBareWriteLink`
passed **546 jobs**; final Plan 1.2 s, Proofs 1.0 s, Link 1.1 s. Fresh audit
checked all **96 declarations in six physical modules**, including private
helpers, transitive types, opaque bodies (`allowOpaque := true`) and inductive
constructors. Only `propext`, `Classical.choice`, `Quot.sound`; no unsafe or
partial logical dependency, zero excluded runtime companions. No sorry,
custom axiom or native decision tactic. Evidence:
`/tmp/xv6-lean-research/SupervisorBareWriteAudit.lean`,
`supervisor-bare-write-audit.log`, `supervisor-bare-write-build.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
