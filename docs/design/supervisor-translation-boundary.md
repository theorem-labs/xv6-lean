# Per-hart supervisor translation slot

This checkpoint ports the source one-shot and the exact resource slot from
RiscvPtsto.v591–596, IntrDefs.v807–916/1178–1268, and SRegime.v352–353/833–837
at paper pin fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. The definitions and
native eighteen-field Spec live in Xv6/Kernel/SupervisorTranslationDefs/Spec.

Capacity is exactly KptResidue.Capacity. Its machine's existing shared
mono-nat ElemG supplies the camera (registry slot3); explicit runtime names
are era.supervisorTranslation cpu. The adapter prevents ambiguous resolution
to another mono-nat camera. Pending is half authority at0, ready is full
at0, shot is full at1, and on is persistent lower-bound1. Two pending halves
can flip once; a lower-bound1 conflicts with pending0, and pending and shot
conflict. Fresh allocation existentially returns a new name (optionally with
a cofinal freshness predicate), rather than claiming allocation at a fixed
existing era name. Four instance contracts and fourteen resource contracts
cover these exact facts and the two slot arms.

The Bare arm owns one pending half, bare, and an existential full stvec
cell. Bare owns existential full SATP with Mode=0 and the complete existing
source PMP config indexed by root0. It does not own a TLB cell. The KPT arm
owns shot and an existential root's complete native KptResidue, including
full SATP/TLB/PMP cells, exact Sv39/asid0/root facts, coherent snapshot,
shared invariant and per-hart credential. It does not own stvec. The generic
slot carries the shared namespace explicitly; sourceSlot uses source kptN.
The slot is a linear disjunction, not a newly allocated Iris invariant.

The Bare accessor consumes the client pending half and dissolves the slot,
returning both halves, bare and stvec. The KPT accessor uses the persistent
on receipt to rule out Bare, returning the actual residue and a wand that
reassembles the slot from that residue. No ghost receipt supplies hardware
truth without the resource arm; in particular flip alone does not install
SATP or publish physical tables.

The coordinator approved the actual compiled signatures. All eighteen native
contracts now compile in670 jobs and pass a strict60-physical-declaration
full type/opaque/constructor audit with zero exclusions. The proofs use
native MonoNat allocation/fractionality/validity/update and ordinary BI
rules, with no custom camera or authority assumption. Final independent
implementation review remains separate; see SupervisorTranslationSTATUS.md.
The source's larger strans_res_at/swp/derived s_regime accessor and execution
contracts (IntrDefs.v1282–1936), operational CSR/SATP/TLB transitions,
per-era name allocation and boot installation remain subsequent work.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
