# PushOffCsr interface review

Independent Codex peer review of root-authored PushOffCsrDefs and Spec:
approved for implementation. This is a signature review, not a claim that
the top CSR plan or native body has been implemented or audited.

The selected source row is push_off+0x0a, index 5, normalized
CSRImm(sstatus,2,x15,CSRRC). Generated execute_CSRImm computes ReadWrite;
doCSR checks access, reads the old status view, computes its complement-2
mask, performs write_CSR, writes the OLD lower_mstatus view to x15, and
returns Retire_Success. The actual write_CSR(0x100) reads mstatus, legalizes,
writes mstatus, and reads it again for its return value. The finite-plan
contract keeps the original actual body, so an unchanged final status does
not erase this intermediate write or the post-write read.

The identity-status result is supported by the completed native
SupervisorSstatusOff component, including arbitrary saved SPELP/MPELP.
The source symbolic shape is WpSconfCsr.v:1629–1688 and
WpGprCsrwCommon.v:291–301. Actual generated paths inspected were
InstsEnd.lean:17817–17820 and ZicsrInsts.lean:7184,18116–18119,22219–22262.
The old-value x15 assignment is correct even though the legalized status
also happens to agree in this disabled specialization.

Config requires only actual Supervisor privilege and source full MISA.
PureSpec.plan separately requires full mstatus/x15 cells and the source
MsFacts/SIE=0 conditions. The native body does not require these pure
conditions from its caller: the existing packet owns msOwnAt and the same
era/hart offToken, whose actual bit agreement gives SIE=0. Its source
MsFacts are already inside msOwnAt. No enabled-arm hypothesis, status
identity oracle, stack bound, memory result or supplied body WP is added.

The same 50-cell regime packet returns with only logical GPR15 changed.
The same control file, all other GPR values, pinned TP, zero-register fact,
status ghost ties, translation residue and literal caller frame are
retained. The actual after register file writes x15; omission of an
additional final mstatus update is justified by the exact identity theorem,
while the plan still must perform its real full-cell write. The six pure
fields and single native CPS field are suitable for the later source
wrapper. Fetch/decode, cycles and complete push_off remain separate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
