# Actual Sv39 TLB fill and direct-slot miss composition

Next root-owned boundary: exact generated add_to_TLB39 at level0, then
translate_TLB_miss39 composed with the frozen actual Sv39Walk and
SupervisorPteAD contracts. No generated-model or earlier owner edit is needed.
Source: VmemTlb.lean287–344 and Vmem.lean474–506 at the pinned model.
Shared table/TLB coherence remains a subsequent source integration rule.

First define the exact level0 entry: asid16, global Boolean, sign-extended
VPN27→45, zero levelMask45, original PPN44, original PTE64 and originating
physical PTE address. Define the actual six-bit hash as the existing tlb_hash
and the actual vectorUpdate of the old64-entry TLB. A native RegisterPlan
must prove the complete read/write/read sequence. The callback's last TLB
read remains in the actual free tree even though its value is unused.
Prove hash<64, exact selected-entry lookup, preservation at every other
index, actual tag matching for the filled ASID/VPN, and the actual lookup_TLB
plan. Foreign tag rejection and global behavior remain explicit in definitions.
The sole footprint is the full actual TLB register; no fresh ghost resource.

Then factor all branches of translate_TLB_miss: walk errors, A/D errors,
Ok none filling the walked word, and Ok some filling the refreshed word.
Compose the already proved three-level walk with the full A/D update and
actual fill. Use the same four physical-prefix cells plus fractional MENVCFG
and full TLB, preserving every other register. The two upper slots can have
arbitrary fractions; the leaf is full at an explicit physical kernel word.
Walked A/D bits remain existential and independent of that physical word.
ADUE is arbitrary: the disabled-update error returns the unchanged TLB.
Only successful paths fill the exact originating address and return leaf PPN,
PBMT_PMA and Unit. No successful response or per-node rule is a caller premise.

Public final resources retain all three slots, original anchors and credential,
three walk view receipts, the A/D branch's exact reservation/receipt, updated
physical leaf word when written, and the exact resulting six register cells.
The final continuation has the three walk guards plus the branch's zero/one/two
memory guards. Actual fill register events are folded separately. No TLB hit,
shared coherence, virtual canonical-address front, enabled handler, boot KPT
publication or translated mycpu theorem is claimed by this direct-slot miss.

Review the initial actual TLB fill Defs/Spec before proof implementation;
review the combined miss signature separately before composition. Kernel-check
all equalities and physically audit every declaration/type/opaque body/constructor.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
