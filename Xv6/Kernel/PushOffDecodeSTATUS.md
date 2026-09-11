# push_off decode: frozen semantic certificates

All six approved contracts are implemented in six modules. Full build:
1,128 jobs. Certificates1.8 seconds, Plan1.3 seconds, Proofs5.6 seconds,
Link1.1 seconds. Strict owner audit checks all83 physical declarations,
including generated/private origins, with exporting=false, collectAxioms
on every root and full types/opaque bodies (allowOpaque=true)/constructors.
Only propext,Classical.choice,Quot.sound; no unsafe/partial dependency;
zero exclusions. No sorry/custom axiom/native_decide/bv_decide.

All24 frozen PushOffCode.decoded rows are now tied to the actual generated
ext_decode_compressed/ext_decode program by finite RegisterPlan.Returns,
with the complete register file unchanged. The row-dependent footprint
is one fractional misa cell for compressed instructions, or fractional
cur_privilege/menvcfg cells for base instructions. Repeated eager reads
remain in the actual Free program; the footprint is not a read-count claim.

Config uses the actual source HardwareConfig.misaC=0x800000000014112d
for compressed rows and Supervisor privilege plus source
Sconf.menvcfgS=0xa000000000000000 for base rows. All other registers remain
arbitrary. The source compressed kd rules often need only misa.C=1;
this component deliberately certifies the stronger source-owned full
hardware value and does not claim the weaker universal C-only theorem.
Base decoding needs no extra misa premise for these five words.

The three JAL-x1 rows reuse KptJal.decode_factor and its checked arbitrary
immediate bitfield reconstruction. The small owned extension plan retains
actual Zihintpause/Zicfilp queries and Supervisor menvcfg read, using no
unrelated full-cycle Config. Existing MycpuDecode.decode13 discharges the
identical C.JR row; the repeated C.LW row reuses its first certificate.
The remaining nineteen certificate declarations construct only Eq.refl;
the Lean declaration kernel checks conversion through actual generated
semantics and snapshotPlanRun. Its read oracle is identically none, so
memory events, writes, errors and missing register values cannot succeed.
The private structural transfer proves complete RegisterPlans; all snapshot
coverage and evaluation facts are supplied internally. nativeSpec has no
caller oracle, Covers, evaluation-success or component-law premise.

For all nineteen compressed rows, actual execute equals pure ExecuteAs of
the exact source normalized AST. This retains one redirection, including
signed C.LW, C.ADDIW and negative C.J immediates, and does not execute that
normalized body. The five base rows are proved equal to their normalized
ASTs. No fetch, normalized CSR/load/store/control instruction execution,
full cycle, push_off function WP or enabled capability transition follows
from this layer alone. Existing byte ownership and source tables are
unchanged; these are the separately linked semantic certificates they
previously lacked.

Sources: complete CodePushOff.v and its referenced KernelDecode shards;
KernelDecode00:60–69, KernelDecode17:365–368, KernelDecode22:240;
actual DecodeExt:204–208, InstsEnd decoder/execute clauses and
PlatformConfig.currentlyEnabled. Source pin:
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.

Reproduction:

- PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.PushOffDecodeLink
- PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/PushOffDecodeOwnerAudit.lean

Evidence: /tmp/xv6-lean-research/push-off-decode-build.log,
push-off-decode-certificates-build.log,push-off-decode-plan-build.log,
push-off-decode-owner-audit.log and push-off-decode-frozen.json.
Design: docs/design/push-off-decode-boundary.md. Independent coordinator
review pending. No frozen source table, previous owner module or umbrella
was edited.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
