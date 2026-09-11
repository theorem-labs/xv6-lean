# Per-hart shared KPT translation residue: contract checkpoint

All four modules Defs, Spec, Proofs and Link compile. `actual` implements
all thirteen approved fields; `nativeSpec` and `registrySpec` discharge the
existing native resource dependencies. The approved Defs/Spec are unchanged.
No CSR/SATP update or translation execution theorem is claimed.

The full source `KptShare.v:153–307` and `SmodePte.v:24–55` were read at pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, together with the actual generated
SATP accessors and existing native TLB/PMP resources.

`SatpRooted` is exactly the conjunction of the three source facts: generated
64-bit mode field is Sv39 (8), zero-extended actual ASID is zero, and the
actual PPN accessor returns the supplied root. It does not assume a stronger
whole SATP constant. `satpCell` and `tlbCell` own the actual generated register
values at full fraction for the specific era and CPU.

`tlbSnapOK` is the existential source `tlb_snap_ok`: the existing exact
`TlbCoherence.Coherent 0` predicate plus a persistent canonical tree snapshot.
The coherence predicate retains foreign VPNs at the same hash slot, stale
A/D variants and the original installing leaf address. Canonical snapshot
agreement permits transport to a separately supplied snapshot; it never
identifies a cached leaf with current physical memory. `EmptyTlb` quantifies
all 64 real optional vector slots, with no hash-injectivity assumption.
The empty-snapshot rule obtains an actual snapshot by native invariant
access with explicit mask inclusion, then derives empty coherence.

`credentials` reuses `KptShared.credentials` without changing its quantifier:
there exists a bound with the matching one-shot/log receipt and this CPU's
boot/view credential. The boot introduction requires `hartAgent cpu = 0`
and the real log lower bound; it does not invent a view receipt.

`pmpConfig` directly reuses the native source `SupervisorPmp.config`. No
source fields are missing: it owns both complete PMP cfg/address vector
cells at full fraction, with entry-zero TOR, strictly positive upper address,
X/W/R all enabled and RAM upper-bound coverage. Later entries, the lock bit
and other fields stay arbitrary. Its existential complete register file
serves only to name these two vectors. The source root-PPN parameter remains
an unused index. MSECCFG, privilege, PMA and HTIF are not part of this source
predicate and are not inserted into the residue. The authority-backed grant
rule reads these same native cells against the supplied real regInterpAt,
returning the equivalent existing TorRam facts; ghost ownership alone does
not assert facts about an arbitrary register file.

`parts` contains all source residue conjuncts, grouping only the three pure
SATP facts. `residue` existentially hides the actual SATP and TLB values.
The proved rules are snapshot/credential persistence, snapshot intro and
canonical coherence transport, empty-TLB snapshot construction, credential
intro and boot intro, residue intro/open, persistent shared/credential
extraction, same-value SATP borrowing with complete reassembly, and the
actual register-authority-backed PMP grant facts.

The SATP borrowing wand requires the same full cell at the same value. It
cannot switch page tables. Whole opening exposes the full resource packet;
rebuilding it requires its complete native cells and logical facts. The
persistent projections do not duplicate SATP, TLB or PMP ownership.

Source mapping:

- `KptShare.v:153–177`: exact snapshot and per-hart credential definitions.
- `KptShare.v:179–221`: full residue, introduction and open representation.
- `KptShare.v:235–278`: shared projection, read-only SATP accessor, and
  authority-backed grant facts.
- `KptShare.v:284–305`: the existing exclusive-to-shared publication door.
  This final publication composition remains separate: the source exclusive
  `tlb_inv_pt` packet is not replaced here by an invented truncated predicate.
- `SmodePte.v:31–55`: exact two-cell PMP predicate, reused unchanged.
- Generated `Vmem.lean:415–427`: actual ASID and PPN projections.

No new ghost capacity or name is required. Later operational TLB fills,
refreshes, SATP switches, translation and boot publication must use their
actual native transitions and return the residue; these definitions do not
supply those proofs.

The native proofs use `KptGhost.agree` at the same era snapshot name for
coherence transport, and actual `KptShared.read_snapshot` with mask inclusion
for empty-TLB construction. The latter applies the checked actual hash-index
bound to the full vector-emptiness hypothesis. The same-value SATP wand
reassembles every original cell, coherence assertion, PMP packet and client.
The grant projection applies native `Registers.reg_valid` twice against the
actual supplied authority, then transports all six TorRam fields through
those two exact vector equalities. Its pure result can be derived while
retaining the original residue in a surrounding frame.

Validation: `python3 tools/lake.py build Xv6.Kernel.KptResidueLink` passed all
722 jobs, with Proofs 1.2 s and Link 1.0 s. Full physical-origin audit:
`/tmp/xv6-lean-research/KptResidueOwnerAudit.lean`; raw build and audit logs
are `kpt-residue-owner-build.log` and `kpt-residue-owner-audit.log` in the
same directory. The audit follows every type, opaque body and constructor,
including private implementation declarations. All 49 physical declarations
across four modules passed with only `propext`, `Classical.choice`, and
`Quot.sound`, zero exclusions and no unsafe/partial dependencies.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
