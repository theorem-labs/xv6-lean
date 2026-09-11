# Independent shared KPT residue review

PASS for all four frozen KptResidue modules and STATUS. All thirteen native
contracts match their stated source boundary. No implementation correction
is required.

I read the complete implementation and compared it to pinned
KptShare.v:153–307 and SmodePte.v:24–55, actual generated SATP accessors,
SupervisorPmp.config/TorRam, KptGhost snapshot/bound agreement, and the native
KptShared.read_snapshot proof. Artifact pin is
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.

SatpRooted contains exactly the source Sv39 mode, zero ASID and root PPN
facts, through actual generated accessors. SATP and TLB cells are the full
native dependent-register fragments at the specific era/CPU name. No whole
SATP constant, CSR transition or equality with an unrelated register file
is substituted. The three facts are grouped into one pure conjunction;
all other source residue legs remain separately owned.

The source tlb_snap_ok existential is retained: single-tree Coherent at
ASID zero and a canonical native snapshot. Transport opens that existential
and uses KptGhost.agree on the SAME era.kernelPageTable name, yielding only
canonical-tree equality. The existing TlbCoherence canonical law then
transports the entire vector. This does not identify cached A/D with current
physical memory or discard foreign tags at colliding hash slots.

EmptyTlb covers all 64 optional vector entries. snapshot_empty obtains an
actual tree snapshot by opening/closing the existing shared invariant under
explicit namespace-mask inclusion, then uses the checked hash bound and
empty-vector hypothesis. It mints no new ghost world, assumes no snapshot
oracle and retains the invariant through its persistent ownership. The
underlying read_snapshot closes the full physical tree/map packet before
returning the persistent snapshot at the original mask.

Credentials preserve the source existential bound and its native one-shot
bound receipt/log lower bound together with the per-hart boot/view credential.
The boot constructor requires hartAgent cpu=0 and the real log lower bound;
it does not invent a view receipt for another CPU.

PMP ownership reuses the exact two full vector cells and all six source
entry-zero facts: TOR, positive upper address, X/W/R bits and RAM coverage.
The existential complete register file only packages those two vectors;
other fields are unconstrained. The source unused root index remains unused.
The predicate does not silently add MSECCFG, privilege, PMA or HTIF facts.
grant_facts uses two actual Registers.reg_valid applications with this era/
CPU's supplied regInterpAt, then transports the six facts through the exact
cfg/address vector equalities. This is the source authority-backed pure
projection, not an assertion that arbitrary register files satisfy PMP.

The introduction/open laws contain every resource leg. Persistent shared
and credential projections do not duplicate any linear SATP, TLB or PMP
cell. The SATP accessor takes one full cell out and returns a wand requiring
that SAME cell at that SAME value; it reassembles the original TLB snapshot,
PMP packet, shared invariant and credential. It cannot perform a SATP switch.
Link supplies the existing native capacities and their concrete registry,
with no added authority or abstract successful-callee assumption.

Fresh build: 722 jobs. Fresh physical-origin audit: all 49 declarations across
four modules, including private/generated declarations, types, opaque bodies
and datatype constructors. Only propext/Classical.choice/Quot.sound occur;
there are no unsafe/partial semantic dependencies and zero excluded roots.
Four independent kernel checks validate the actual SATP fields: rooted Sv39
acceptance, Bare rejection, foreign-ASID rejection and wrong-root rejection.
All four checks use standard axioms only. Evidence:

- /tmp/xv6-lean-research/KptResiduePeerAudit.lean and kpt-residue-peer-audit.log
- /tmp/xv6-lean-research/KptResiduePeerChecks.lean and kpt-residue-peer-checks.log
- /tmp/xv6-lean-research/kpt-residue-peer-build.log

The source exclusive-to-shared publication door at KptShare.v:284–305 is
explicitly outside this four-module package. No source boot, physical table
publication, CSR update, full translation or cross-backend equivalence is
claimed by this review. STATUS accurately records those limits.

Frozen module SHA256:

- Defs: `5ea17cd6d663e7ede16a955a520d074d5fac3abbe3bfcb3e6ca38a18f8af2c0a`
- Spec: `f92c9cde62b269807f31881f5cde8a2c1d94a90d5047f934f0593d1da70c36e8`
- Proofs: `767bbbbb6af4763a55e057947071a1d1c37cd135684533f1ed993bc43f01640a`
- Link: `47abf69a93dedd39410ae7af547e4f2bd85e2f783deeaadd2118985fac4c79db`

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
