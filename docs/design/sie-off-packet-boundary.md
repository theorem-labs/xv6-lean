# Source disabled capability to the native cycle packet

The actual SieOffPacketDefs/Spec checkpoint is a resource adapter, with no
instruction WP or successful-execution premise. Its input is exact native
SieOffCapability.gpr and SupervisorRetirement.pcIs at the same era/hart.
Sources: IntrDefs.v595–686/2762–2769/3224–3270 and InstrBytes.v701,
MinstretInv.v349–366, pinned fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.

The fifty physical cells are paid once each:

- Nine source pc_is cells: PC/nextPC, minstret/increment, discarded
  mcountinhibit/minstretcfg, and full mcycle/mtime/mip. The original reservation
  resource remains separate, as in pc_is.
- Five full Sconf cells: privilege, mstatus, mie, mideleg, menvcfg.
- Four discarded hardware cells: misa, pma_regions, HTIF base and elp.
- One full HART_ACTIVE cell and31 actual HartTp GPR cells. x0 is its existing
  logical zero fact and TP is the real per-hart pin, not a duplicated cell.

The open rule constructs an existential symbolic control file from these
owned values. It makes no claim about unowned physical register projections.
Its Ambient fields retain all source configuration constraints relevant to
this footprint, including the general PmaClass predicate. It derives disabled
SIE from the actual msOwn half/off eighth. Native MycpuRegimeShell.partition
exposes the exact50-cell footprint, bit frame, x0 and actual translation lane.

An explicit remainder keeps the actual available KernelStack, running
context, per-hart timer, tier witness, whole persistent hardware config and
linear slot token. Keeping the whole hardware config retains mseccfg,
senvcfg, scounteren, mhpmcounter, all static claims and the actual generation
certificate, while its four discarded cell copies can be read by the packet.
No context, full register cell or stack word is duplicated.

The source slot is opened by its real disjunction. Bare contributes its
actual bare physical resource to the packet and retains pending plus stvec;
KPT contributes the actual existential-root residue and retains shot. The
proof-side Regime fixes the source kptN; it cannot select an unrelated
invariant namespace. At full tier, real kptOn conflicts with the Bare pending
half. Therefore Admits is a *derived* pure output, never a replacement for
the source tier receipt. Reassembly uses the retained exact token and returned
translation resource, including any correctly updated coherent TLB residue.

close_packet takes the actual returned opened resources and source Boundary
facts: PC/nextPC agree, hart is active, privilege remains Supervisor, mie is
the source literal, mideleg delegates it and menvcfg has its four facts and
literal. Returned msOwn contains its own full status/ghost/facts; no arbitrary
mstatus restoration oracle is needed. Clock/retirement and GPR values may
change. The remainder's stack must correspond to the supplied current file
and available count; native push/pop laws can transform it beforehand. The
same context, tier, era and hart remain explicit. No unrelated-file equality
or assumed instruction correctness appears.

Five actual contracts: open, close, exact partition, persistent certificate
extraction, and an optional boot-PMA resource bridge. The unchanged approved
signatures and complete native implementations compile in931 jobs. A private
structural projection avoids expanding the large static map in proofmode;
its public instantiation retains the exact original hardware bundle.

The execution limitation is substantive: source hardware config gives
PmaClass.allowsAll, not regions=pmaBoot. Existing MycpuBare.SupervisorConfig,
KptAddress.Ambient and downstream KptMemory/fetch plans require literal
pmaBoot equality. The general open rule deliberately does not produce those
stronger execution configurations. boot_pma_from_cell is separately named
and requires an actual same-hart discarded pma_regions↦pmaBoot fragment;
native register agreement can then derive equality while returning the
opened packet. It is not a new pure assumption added to source Sconf, and
this adapter does not allocate that extra fragment or claim boot established it.

To close a general source function adapter later, either generalize the
actual PMA plans using the proved class access/grant obligations, or establish
and carry actual boot-PMA ownership at the boot boundary for an explicitly
specialized theorem. Current translation/read/write/fetch success theorems
cannot be applied to arbitrary source Sconf by packaging alone. Separately,
full function/body composition, code-span resources and native boot
inhabitation remain outside this resource adapter.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
