# Disabled supervisor source packet: frozen native adapter

All five approved contracts are implemented in five modules. Full build931
jobs (Resources1.4s, Proofs1.5s, Link1.2s); strict owner audit covers all123
physical declarations, including private/generated declarations, with
exporting disabled and full types, opaque bodies (allowOpaque=true) and
constructors. Standard three axioms only; no unsafe/partial dependency and
zero exclusions. No sorry/custom axiom/native_decide/bv_decide. Generic
nativeSpec and the existing48-slot registrySpec discharge all fields without
supplied component laws, execution results or restoration callbacks.

Source mapping: IntrDefs.v595–686/2762–2769/3224–3270, InstrBytes.v701 and
MinstretInv.v349–366, pinned fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.
This combines already native source Sconf, disabled capability, HartTp file
and pc_is resources into the actual MycpuRegimeShell packet. It does not
port an additional instruction theorem or assert a source function WP.

- open_packet constructs the symbolic control projections from actual
  source cell ownership: pc9, Sconf5, discarded hardware4, active1 and31
  GPRs. It derives the source Ambient facts, including general PmaClass and
  disabled SIE. It retains the native bit frame and original reservation.
- split_slot/join_slot preserve the actual Bare versus KPT disjunction.
  Bare retains pending/stvec; KPT retains shot and the original namespace.
  Bare at full tier is excluded by the actual on/pending ghost conflict.
  Admits is derived from resources, never substituted for a tier receipt.
- close_packet consumes the actual returned packet and its exact remainder.
  Only owned Boundary projections are constrained. Changed GPRs, clocks,
  status and a correctly updated coherent TLB residue can reassemble when
  their real source resources are returned. No full-file equality is assumed.
- partition reuses the native disjoint50-cell partition. Stack, running
  context, timer, tier witness, whole hardware config and linear slot token
  remain explicit. Whole hardware preserves all security/counter/static-map
  resources and the generation certificate; only discarded cells are copied.
- certificate extracts the real native generation certificate and preserves
  the same packet. boot_pma_from_cell derives literal boot-PMA equality by
  agreement with an additional actual same-hart discarded register fragment.
  It does not allocate that fragment or infer literal equality from PmaClass.

Resources.assemble sets exactly the control projections supplied by the
owned components; unrelated projections inherit the source pc_is witness
without asserting they equal the physical register file. The private
trim_hardware theorem is a generic BI structural projection, instantiated
with the exact native static map. This avoids proofmode expanding49k map
claims while retaining the complete original hardware bundle. It is not a
public resource assumption.

Reproduction:

- PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.SieOffPacketLink
- PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/SieOffPacketOwnerAudit.lean

Evidence: /tmp/xv6-lean-research/sie-off-packet-build.log and
sie-off-packet-owner-audit.log. Coordinator independent review is pending.

The general-PMA versus boot-specialized execution gap remains explicit:
existing translation/fetch/memory configurations require literal pmaBoot.
This resource adapter retains the weaker exact source hardware predicate.
Actual PMA generalization or a separately established boot-PMA fragment,
code resources, complete function composition and native boot inhabitation
are subsequent obligations. No new camera, generated model, prior owner
module or umbrella was edited. See docs/design/sie-off-packet-boundary.md.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
