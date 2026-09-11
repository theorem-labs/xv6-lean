# Supervisor PTE A/D composition: independent peer review

PASS for the declared direct-slot contract. Codex subagent artifact_audit
independently read all eight frozen SupervisorPteAD modules, their Spec,
STATUS and approved design. The implementation was authored by another
agent; this review did not edit implementation files. No correction is
required for this scope.

Reviewed source is xv6iris
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476:
PtTreeAdue.v:1650–1818 and 1852–2045, including
swp_update_and_write_pte_upd and swp_update_and_write_pte_ex;
HartSKpt.v:730–910, especially kpt_leaf_write_node and its per-byte
floor/anchor reconstruction. I also compared the complete generated
Vmem.update_and_write_pte:325–360, the relevant check_leaf_pte tail,
PlatformConfig's Svadu/Svade definitions, the actual KptLeaf plan and the
native PTE read/write contracts and blocked-event implementations.

The program factor is an equality to the actual generated tree at Sv39,
level zero, Supervisor. It preserves the outer cached test, the full gate,
exclusive reread, validation of that reread, the second update test, and
all original response tails. In particular, cached None does not read
menvcfg; disabled ADUE returns NeedsUpdate; reread/check/write errors retain
the source propagation; conditional write Ok false is the original
internal_error, not a retry. Its unreachable-success exclusions come from
owned native memory/validator proofs rather than deleting branches from
the factor.

The pinned pure feature definitions make Svadu and Svade true. The eager
Lean gate still performs its actual menvcfg read, including when ADUE is
false. No true-ADUE premise is added. The five-cell footprint is the four
PMA/PMP/HTIF cells plus menvcfg, with explicit fractions and uniqueness.
The KptLeaf validator keeps all seven eager register reads through
universal readAny branches and needs no duplicate ownership or fixed
unowned register value. Its RX/RW leaf family has zero extension bits and
arbitrary PPN/A/D; Supported/Allows restrict precisely fetch, Data load,
Data store and Data AMOSWAP with arbitrary aq/rl. This is why arbitrary
MXR/SUM and PBMTE-dependent reads still validate the same leaf.

All four final branches agree with their actual returned word and
reservation. Cached and disabled preserve the incoming reservation.
Reread/no-write keeps the exact physical-word snapshot and returns a read
view receipt. Written returns reservation none, the new full slot, positive
authored time, logElem(time−1) for the exact eight-byte write and the view
receipt at that time. The cached and physical A/D values are independent;
inner behavior is computed from the physical reread, never substituted
from the cached word. BranchFacts are proved from the actual equations.

The native continuation pays zero guards for cached/disabled, one for
reread and two for written. The source register events are separately
folded; no pure-return branch is charged a fictitious memory guard. The
reread rule preserves actual reservation-clearing retries on blocked
exclusive reads. Conditional writes retain their snapshot and original
state while blocked. These WPs provide no eventual-completion theorem.

Resource reconstruction is exact. collect_floors uses a duplicate-free
finite list to expose the existing eight existential floors. slot_open
separates the full pin window from the original floor bounds and
publication anchors. slot_close returns those same floors, bounds and
anchors after the native authored write. The proof establishes the needed
opening/closing entailments; it does not export an additional general
bidirectional slot equivalence. update_canonical and canonical_members
prove new-byte membership in the unchanged canonical family, with no
fraction upgrade, new publication credential or invented no-wrap premise.
Both memory wrappers restore all five register cells. Public nativeSpec
internally discharges the actual KptLeaf/native memory implementations;
there is no caller-supplied validator or preservation oracle.

The material source boundary remains explicit: this theorem owns the full
physical slot continuously. It does not implement the predicate-indexed
shared KPT reread accessor or hold an invariant open across several free
events. The source shared-table theorem must release/reacquire per-node
resources and admit a physical word selected by interference. The direct
contract, although allowing different cached/physical A/D bits, is not that
shared-accessor theorem. Tree invariant preservation, complete walking,
TLB behavior, the KPT function regime, cross-prover correspondence and
whole-xv6 adequacy are not consequences of this component.

Independent validation:

- `python3 tools/lake.py build MachCSL.Logic.SupervisorPteADLink` passed all
  658 jobs against the frozen source files.
- A separately run strict physical-origin audit checked all 396
  declarations in all eight modules, including private definitions,
  proposition types, opaque bodies with allowOpaque=true and constructor
  fields. It allowed only propext, Classical.choice and Quot.sound and
  rejected every unsafe/partial declaration anywhere in the logical cone.
  There were zero exclusions.
- Evidence: /tmp/xv6-lean-research/SupervisorPteADPeerAudit.lean and
  supervisor-pte-ad-peer-{build,audit}.log. No compiler installation,
  generated model or owner implementation was changed for this review.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
