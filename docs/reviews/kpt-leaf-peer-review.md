# Independent kernel leaf validator review

PASS for the declared concrete word and actual level-zero Sv39 validator
scope. This review was performed by the Codex lean_logic_audit subagent,
independently of the coordinator who implemented the five modules.

I read KptLeafDefs/Spec/WordProofs/Plan/Link and STATUS in full, compared the
complete contracts to pinned KptPt.v:428–454,706–795 and Pt4kWalk.v:26,
and inspected the actual generated invalid-PTE, permission and
Vmem.check_leaf_pte programs. The source pin is xv6iris
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476; generated model provenance remains
the repository's recorded pinned model and adapter, with the general
cross-prover correspondence obligation unchanged.

The exact RX/RW bases, arbitrary A/D bits, symbolic 44-bit PPN, ten low
flags and zero upper extension bits agree with the source construction.
The bit proofs establish actual generated field extraction and setters;
canonicalization clears only A/D. Leaf classification is supplemented by
the proved invalidity and permission checks, rather than being treated as
sufficient validity on its own.

Supported accesses are the four source cases: fetch, Data load/store and
AMOSWAP with independently arbitrary aq/rl. Fetch requires RX; writes
require RW; both families admit loads. SUM/MXR are arbitrary. The actual
permission program is pure; the invalidity and complete leaf programs are
not identified with pure programs. Their empty-footprint plans retain all
five and seven eager register reads respectively, with each returned value
universally quantified. The actual level-zero branch preserves the PPN;
zero extension bits discharge NAPOT and both PBMTE branches without assuming
fixed MISA or menvcfg values. No superpage, shared KPT accessor or address
translation theorem is inferred.

Fresh independent physical-origin audit checked all 292 declarations in
all five modules, including private helpers, declaration types, opaque
proof bodies and inductive constructors. Only propext, Classical.choice
and Quot.sound occur; zero exclusions and no unsafe/partial logical
dependencies. Evidence is /tmp/xv6-lean-research/KptLeafPeerAudit.lean and
kpt-leaf-peer-audit.log. The completed dependency was also rebuilt while
checking the native A/D composition. No source or proof correction was
needed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
