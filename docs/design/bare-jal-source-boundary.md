# Actual identity/Bare JAL x1 source branch

The coordinator approved the six-module, 605-job Defs/Spec checkpoint.
All 24 contracts are now implemented in 22 modules, with a 1,196-job native
Link build and strict 204-declaration audit. The final source rule supplies
all actual fetch, decoder, JAL, retirement, clock and restart WPs internally.
The audit includes private declarations, opaque bodies, types and datatype
constructors, permits only the standard three foundational axioms, and
excludes no declarations. No initial-allocation dependency is present.

Source pin: xv6iris arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. Read the exact
`WpSconfCtl.v:237–281` JAL rule, complete `SpecMycpu.v` and `ProofMycpu.v`,
`SRegime.v:823–861` Bare ownership, and the stack/context definitions cited
in the independently reviewed MycpuBareSource adapter. The generated
`fetch`, `fetch_bytes`, `execute_JAL`, decoder/encoder and cycle behavior
are the same pinned programs already used by the completed KptJal proofs.

## Generic physical fetch: BareJalFetch

The actual nine-cell footprint is PC/MISA plus the existing seven
SupervisorBareFetch cells: mstatus, current privilege, SATP, PMA regions,
PMP configuration/address vectors and HTIF base. The component Config
states the actual sufficient Bare/Supervisor/SXL fields, owned TOR-RAM PMP,
explicit pmaBoot, HTIF-none and MISA.C. These are derived inside the source
route, not supplied as configuration or success assertions by its caller.

Code is exactly existing identity-tier `KptFetch.instrBytes` for an arbitrary
F_Base word. It includes two-alignment, non-RVC classification, and all four
native virtual RX/pristine bytes. KernelTextDatum identity access produces
the actual physical bytes/pristine timestamps and its context conversion
produces the native context read window. A nonempty window yields actual
physical text membership from the owned claim. Text membership, supported
width and alignment justify the RAM/PMA/PMP obligations; no caller physical
word, successful translation/read or fixed read-view proof is accepted.

The generated outer factor and KptFetch.Plan/Chunk vocabulary are reused.
The actual program makes one four-byte read when PC is four-aligned, and
two two-byte reads otherwise. At offset 4094 both halves are read at their
own addresses; no word-aligned or single-read restriction is introduced.
The raw generated factor and chunk OneRead tail retain the actual error
branches. The successful native route follows from the source ownership.

`guardReads` is a finite fold with one actual later and universally
quantified returned view per read, in read order. Its receipt ledger contains
every returned native view lower bound. The full fetch returns all nine
cells, running context and original persistent code. Ordinary instruction
reads leave a framed reservation unchanged; they do not install any TLB
entry or KPT residue. The chunk WP is an internal primitive, and the final
fetch implementation must supply it rather than accepting a chunk-WP oracle.

## JAL on the source packet: BareJal

The component uses the existing sourceShares and fifty-cell
MycpuRegimeShell packet at its actual `.bare` lane. The three additional
translation cells are existentially owned by that lane. An explicit
53-cell footprint and filtered forty-four-cell remainder specify the reversible
nine-cell fetch partition, with all bit ties and the zero-register fact
retained. The patch changes only the three SATP/PMP projections. Its values
come from actual native ownership by opening MycpuRegimeShell.partition
and its Bare translation assertion (the same carrier as MycpuBareSource.packet); arbitrary
unowned projections of the original control file are never asserted to be
physical state. The same control interpretation returns after fetch.

KptJal's completed generic bitfield, decoder, preparation and JAL register
plans are reused. There is no second generated-decoder normalization.
Source code alignment plus the target-even premise derives exact immediate
encodability. Preparation writes nextPC=P+4; actual JAL reads that link, sets nextPC to
the target in jump_to, then writes RA=P+4 on success, preserving SP/TP and all
other GPRs. The raw failure branch and eager extension/MISA reads remain.

The four native contracts are full fetch, body, active execution and actual
cycle. They return the same packet and running context, all physical-read
guards and view receipts, original instruction ownership and arbitrary
frame. Fetch/active preserve the framed reservation; actual restart clears
it. Cycle completion uses the real shell Completed relation, optional clock
choices and guarded next-cycle continuation. No successful fetch, decoder,
body, retirement or execution WP is a caller premise.

## Opened source branch: BareJalSource

The public input is the actual identity-tier **opened Bare arm** from
SieOffPacket, its already-derived Ambient facts, the native JAL instruction,
a same-hart discarded pmaBoot cell and arbitrary caller frame. Identity tier
alone does not select Bare. A separate dispatcher must choose between this
arm and identity-tier KPT. No source-stack lower bound appears: JAL moves
no SP and uses no scratch slots.

Native entry opening derives the configuration by agreement with the
explicit boot-PMA cell and the supplied Ambient facts. `kept` names the
entire unchanged virtual stack, timer, tier witness, full hardware, actual
pending/stvec slot token, boot-PMA ownership and caller frame. The running
context is separated once for actual reads. Certificate access comes from
the same hardware assertion; there is no fresh world or authority allocation.

After the actual cycle, the source Boundary at the exact JAL target follows
from Completed. The unchanged SP proves the whole original stack assertion
is still suitable for the updated file. Source closing returns the actual
SieOffPacket input at target, updated RA, unchanged available count and
retained instruction/PMA/frame. The only public WP premise is the genuine
returned-cycle continuation. Persistent read receipts may be kept internally
when this resource-only source wrapper closes, as in the source rule.

Ownership is limited to new BareJalFetch, BareJal and BareJalSource modules,
BareJalSTATUS.md and this design. No frozen implementation, image, decoder,
camera, registry or umbrella is changed. The source JAL/mycpu callable
composition, general-PMA extension, source entry inhabitation and boot
reachability remain subsequent dependencies. Validation evidence:
`/tmp/xv6-lean-research/bare-jal-all-signatures.log`,
`bare-jal-source-link.log`, `BareJalOwnerAudit.lean`,
`bare-jal-owner-audit.log`, `BareJalChecks.lean`, and `bare-jal-checks.log`.
The 31 kernel-checked edge fixtures cover signed negative immediates, odd
immediate rejection, PC mod 4 = 2, offset 4094 across pages, exact low/high
halfwords and original fetch start, 53 = 9 + 44 unique-cell partition,
unchanged SP/TP and exact three-field control patching.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
