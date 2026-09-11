# Independent Sv39 TLB insertion review

PASS for the declared level-zero insertion and immediate-lookup scope. I
independently read all four coordinator-authored `Sv39Tlb{Defs,Spec,Proofs,Link}`
modules and the complete generated `LeanPaperStock/VmemTlb.lean`, then rebuilt
and audited the implementation. No correction was required.

The six contracts match the actual functions. `index` is the low-six-bit
`tlb_hash 39`, and its bound is proved from the bit-vector bound. `entry`
retains the supplied ASID, arbitrary global bit, raw PTE, physical `pteAddr`
and PPN; its VPN is sign-extended from 27 to 45 bits and its level mask is
zero. This is precisely `add_to_TLB` at level zero: both PPN/VPN clearing masks
are zero, without a stronger canonical-address or PTE-validity assumption.

`filled` uses the actual Sail vector update. `selected` establishes the exact
nested `some` result at the selected index; `other` preserves every other
lookup, including out-of-range optional lookups. The read/write/read sequence
in `fill_plan` preserves the final callback read. That read is universal
because the generated callback discards its argument; it is not erased or
replaced by an assumed post-write value. The first read and write use the
single full `.tlb` cell and preserve all unrelated registers.

`lookup_plan` performs the actual TLB read, proves the selected array entry
exists, and uses `match_TLB_Entry` with the same ASID and VPN. Its proof covers
both values of the global flag. It returns the exact hash index and entry,
with unchanged post-insertion registers. There is no assumed lookup result,
evaluator certificate, memory-read oracle or logical TLB interpreter.

This layer does not prove a translation, TLB coherence with physical page
tables, foreign-tag lookup behavior, stale A/D refresh, flushing, or a native
instruction WP. In particular its arbitrary PTE/PPN/address inputs are data
for the insertion function; the contracts do not claim those fields describe
a valid mapping. Higher-level walk and shared-invariant proofs must supply
that relationship.

Validation:

- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.Sv39TlbLink`
  passed all 427 jobs. Log: `/tmp/xv6-lean-research/sv39-tlb-peer-build.log`.
- `/tmp/xv6-lean-research/Sv39TlbPeerAudit.lean` selected all 33 physical
  declarations in the four modules. The independent audit followed all
  declaration types, opaque bodies (`allowOpaque := true`) and inductive
  constructors, with zero exclusions. Only `propext`, `Classical.choice`,
  and `Quot.sound` occur; no unsafe or partial semantic dependency occurs.
  Log: `/tmp/xv6-lean-research/sv39-tlb-peer-audit.log`.

The implementation and review were performed by distinct AI-agent roles in
the same team; this is not a human review.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
