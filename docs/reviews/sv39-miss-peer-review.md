# Independent native Sv39 miss review

PASS for the six frozen Sv39Miss modules (Defs, Spec, Factor, Rules, Proofs,
Link), their STATUS, and the stated direct-slot boundary. No semantic or
resource correction is required. During review, the owner moved four helper
definitions from Factor/Rules to Defs; theorem bodies and APIs were unchanged.
This report covers the final layout.

I read the complete implementation and compared its factorization to the
actual pinned generated Vmem.lean474–505 (`translate_TLB_miss`) and
VmemTlb.lean287–344 (hash, lookup, level 0 fill and callback), together with
the already reviewed native three-level Sv39Walk and full SupervisorPteAD
branch contracts. The general factor equations preserve every walk/update
error before the supported-slot specialization. Both successful update forms
retain the walk's PPN, PBMT, originating PTE address and global flag. A cached
success fills the walked word; exclusive reread fills the physical word; a
write fills the newly written word. Disabled ADUE returns the precise error
without modifying the TLB. No branch substitutes a successful response.

The six-cell native footprint splits into the actual four-cell read prefix,
MENVCFG and TLB; A/D receives its original five cells while the full TLB is
framed. Fill uses a proved actual register plan with read/write/read, including
the callback read whose value is unused. Its readAny rule quantifies over the
actual result and does not erase that event. Unique-key checking supports the
native fold; no cell is allocated or duplicated. The physical leaf's full
share is independent of the ordinary walk's cached A/D bits. The two upper
slots retain their arbitrary source fractions and byte views.

The final predicate returns all three slots, updated physical leaf ownership,
original credential/floors/anchors, three walk view receipts, the exact
branch-dependent reservation and receipt, and canonical physical-word equality.
The continuation receives precisely three walk guards followed by zero, one or
two A/D memory-event guards. No extra terminal guard or open invariant crosses
the composition. Link supplies the actual implementations at the current
capacity and has no abstract successful-callee hypothesis or initial allocator.

Six independent kernel sensitivity checks passed: cached versus physical word
selection, reread selection, written-word selection, disabled TLB preservation,
foreign-ASID rejection for a nonglobal entry and foreign-ASID acceptance for
a global entry. This last pair checks the actual generated tag matcher used
by the fill/lookup dependency. All six checks have only standard axioms.

The fresh physical-origin audit checked all 89 declarations, including private
helpers, declaration types, opaque bodies and datatype constructors. It found
only propext/Classical.choice/Quot.sound, no unsafe/partial logical dependency,
and zero excluded roots. The independent build invocation also passes the
final 675-job target. Evidence is retained at:

- /tmp/xv6-lean-research/Sv39MissPeerAudit.lean and sv39-miss-peer-audit.log
- /tmp/xv6-lean-research/Sv39MissPeerChecks.lean and sv39-miss-peer-checks.log
- /tmp/xv6-lean-research/sv39-miss-peer-build.log

Scope remains exact: flag-one/G=0 upper pointers, three supplied physical
slots and supported permissions/access. This does not establish shared KPT
ownership, arbitrary raw G/RSW behavior, TLB-hit coherence, absent-map faults,
virtual canonical-address entry, or translated mycpu from actual boot. STATUS
states those remaining boundaries explicitly.

Final SHA256: Defs 0e65f6ab1ee87c528d4a1d37141a1edf8dfe42414faf3f4888e68f1881f6d01e;
Spec bbe12e276796bdc8e40d4b26b9addc90981bc1faf12b43ecf66153f4541758b1;
Factor 300910904e88e9053e2daddd5b6f524616d229468a898fc540a9dc5831695133;
Rules da2cf247e8f5ccccc45977a063ad75e7f99cf023448a6d13f3087cfe93fb5497;
Proofs 543d74ae699a7a5b34be59aebe085243e1a70cf45b69132eb748b1188dbebd67;
Link d6098d9431c6850aea3cd38d526112aff5d83be2ef581306ed412c1e8d9bf0dd.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
