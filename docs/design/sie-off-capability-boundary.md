# Exact disabled supervisor capability

This checkpoint specializes source sie_cap/sie_cap_gpr to b=false. It reads
IntrDefs.v1968–2062,2660–2950,3184–3276,3358–3420,3470–3560; the source
trap_res definition at573 and tier witness SRegime.v1750–1792 are essential.
All sources are pinned at fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.

The six native capability conjuncts are the actual virtual/context stack,
SupervisorTranslation.sourceSlot, SupervisorBits.offToken, actual running
context, per-hart TimerCap, and the source tier witness. Disabled trap_res
is exactly zero, so stack depth is the caller's available count. The source
process-pointer argument is unused in the false arm and omitted from this
specialized interface. No enabled-arm predicate, handler WP or reserve size
is invented.

The tier witness is emp at identity/KT0 and the actual persistent
SupervisorTranslation.kptOn receipt at full/KT1. It is independent of SIE
and is never replaced by MycpuRegimeShell.Admits. Identity-tier mapping and
RW/positive/RAM claims stay inside each actual KernelDatum word comprising
the KernelStack; the emp witness does not manufacture identity translations.
Full tier needs the real monotone shot receipt even with SIE disabled. The
tier-up contract therefore retains the source explicit kptOn premise as well
as Tier.Le. It cannot lift an arbitrary Bare capability at zero resource cost.

Capacity is exactly MycpuRegimeShell.Capacity, so native stack, translation,
registers, context views and bit ghosts share their existing capacities and
era names. Translation uses the source kptN specialization. No registry or
camera is added. The GPR wrapper adds full actual HART_ACTIVE ownership,
complete native Sconf, and HartTp.pinnedFile: all31 real GPR cells plus
logical x0 and real per-hart TP pin. No pure file stands in for these cells.

Nineteen native contracts are proposed in the actual Defs/Spec checkpoint:
three tier-witness laws; six-conjunct intro/Bare intro/open; persistent timer
and witness borrowing; receipt-paid tier upgrade; same-SP retarget and exact
push/pop/grow/shrink; two actual stack words with a reassembly wand accepting
new contents; exact GPR open/join and source sconf_at boundary open/close.
The two-word accessor captures the actual deeper stack and all other cap
resources, without copying either word or the running context. All moves
retain the source modular paStk and k≤available premises, with no added
global stack bounds or context reindexing.

This is a resource component only. There is no CSR/SIE transition, scheduler
migration, enabled handler, boot establishment, instruction/cycle WP or full
mycpu function theorem. The existing native prerequisites cover every
proposed resource law; no restoration or physical truth callback is needed.
The coordinator approved all nineteen actual signatures. All four native
modules now compile in917 jobs; a strict67-physical-declaration complete
type/opaque/constructor audit passes with zero exclusions. Independent final
review remains separate. See SieOffCapabilitySTATUS.md for proof mapping.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
