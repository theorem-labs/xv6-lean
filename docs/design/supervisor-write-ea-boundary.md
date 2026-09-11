# Supervisor write-address announcement boundary

The coordinator approved this bounded implementation by the Codex Lean-logic
agent. Own `MachCSL/Logic/SupervisorWriteEA{Defs,Spec,Plan,Proofs,Link}.lean`
and STATUS; leave frozen SupervisorMemOuter and generated sources unchanged.

The exact program is `mem_write_ea (Physaddr address) 8 (Store Data) PBMT_PMA
false false false`. It performs six actual reads in this order: mstatus,
current privilege, PMA, PMP configuration, PMP configuration, PMP address.
All five distinct cells have independent arbitrary fractions. No register is
written; the actual `write_ram_ea` is pure unit. There is no HTIF read, MMIO
check, memory write, reservation update, or log append in this prefix.

Pure conditions are actual Supervisor privilege, MPRV clear, the existing
positive supervisor TOR/RAM grant, width-eight RAM interval, an actual matched
PMA region with writable permission, and explicit eight-byte physical
alignment. They constrain neither a reset register file nor unrelated status
bits. No physical memory or context assertion is required for a register-only
announcement, and no returned word or subordinate WP is a premise.

Construct `RegisterPlan.Returns footprint rs program (Ok ()) rs` from the
frozen effective-privilege, PMA-priority and PMP plans, preserving the actual
singleton splitting loop and zero-offset address arithmetic. Prove native
`certificate -∗ cells -∗ (cells -∗ WP (k (Ok ()))) -∗ WP (program >>= k)`
using the existing native register fold. It permits arbitrary resources to
be framed and preserves separate machine event boundaries.

Source pin: xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`,
`HartSMem.v:2845–2928` (`swp_mem_write_ea_S`). The later source virtual-store
proof explicitly performs this announcement before `mem_write_value`
(`HartSMem.v:3229–3245`). The generated definitions are `Mem.lean:497–530`
and `PhysMemInterface.lean:329–331`; `VmemUtils.lean:399–407` likewise retains
both stages. Source generic width/access abstractions are specialized to the
ordinary eight-byte Data case and replaced by actual proved PMA/PMP facts.

The subsequent Bare virtual-memory composition must prove address formation,
translation and exact no-split branches rather than assuming a translation
WP. This announcement slice alone establishes none of those claims, and
must not be conflated with the actual store event. Validate its full proof
cone using the standard-three-axiom audit, with types, opaque bodies and
constructors, without native decision axioms or source edits.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
