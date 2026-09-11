# push_off normalized scalar bodies

The six-module native implementation is built in 931 jobs. Its unchanged
approved Defs/Spec expose twelve pure contracts and one native body rule.
The owned modules are PushOffScalar Defs/Spec/Pure/Plan/Proofs/Link, plus
STATUS. No existing family or umbrella is changed.

The input program is literally execute(PushOffCode.normalized(index i)).
It does not include compressed expansion or the native decoder: the separate
PushOffDecode certificates establish those boundaries. Source inventory is
CodePushOff.v:47–140, pinned at fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.
ProofPushOff uses these facts at 378,486,501,648,692,731,803,832,848,884 and
1069. Generated bodies are InstsEnd.lean:17195–17205 (shift),17263–17288
(ADD),17459–17499 (JALR/JAL/immediate),17853–17866 (branch),17965–17970
(ADDIW); jump_to is BaseInsts.lean:249–261, and the return's actual LPE
callback is ZicfilpRegs.lean:242–252.

| Source index | Offset | Normalized effect |
| --- | --- | --- |
| 0 | 0x00 | x2 := x2−32, modular 64-bit |
| 4 | 0x08 | x8 := x2+32 |
| 6 | 0x0e | x9 := x15; generated x0 source is pure zero |
| 9 | 0x16 | if actual x15=0, nextPC := PC+22; otherwise leave nextPC |
| 12 | 0x1e | x15 := signExtend32(low32(x15+1)) |
| 17 | 0x28 | x2 := x2+32 |
| 18 | 0x2a | nextPC := actual x1 with low bit cleared |
| 20 | 0x30 | x15 := logical right shift of x9 by one |
| 21 | 0x34 | x15 := x15 AND 1 |
| 23 | 0x38 | nextPC := PC−32; discarded x0 link destination |

All untouched GPR values, physical PC and controls other than nextPC remain
unchanged. The explicit physical after-file and software afterValues/
afterControl are proved equal through full entry-file projection. No
integer overflow bound is imposed: arithmetic and ADDIW wrap exactly as
the generated machine operations do. No assumption fixes saved status,
noff, SP, RA or the branch outcome. Taken source branch9 reaches index19;
source jump23 returns to index10. These addresses follow from the table,
while the generic body accepts arbitrary even PC for these two operations.

Arithmetic cases have Config=True. Branch/jump Config is actual MISA.C=1
plus even PC; return Config is the existing minimal Supervisor/LPE-disabled/
C-enabled MycpuReturn.Config. A pure sourceConfig contract derives each
case from source MISA, privilege, MENVCFG and the exact inventory PC. There
is no reset snapshot or PTE/translation-success condition. The branch's
alignment condition is a source-applicable sufficient hypothesis even when
untaken; it does not insert a PC or MISA read on the untaken path.

The actual BEQ reads x15 and the pure x0 value before testing; only a taken
branch reads PC, calls jump_to and reads MISA. jump_to retains its target-bit
assertion, extension callback and eager Zca/C check. Return retains the
privilege/MENVCFG LPE checks, discarded nextPC link read, actual RA read,
low-bit clearing, MISA read and pure x0 write. C.J likewise retains the
nextPC read even though x0 discards the link. Failures are kept in the
actual generated program; the Config and arithmetic proofs justify the
success result, with no caller-selected outcome or successful-body premise.

Native ownership uses the existing common fifty-cell packet, parameterized
by its actual Regime and arbitrary shares for the nine control components.
The two interpretations are the actual existential Bare SATP/PMP assertion
and the actual shared KPT residue. The register-only fold frames this exact
resource unchanged, along with native mstatus bit ties and x0; it creates
no duplicate translation or GPR ownership. The literal caller frame can
contain a reservation, running context, anchored stack words, code and
other resources. SP changes do not silently reindex that frame. The input
packet is the existing disabled-SIE resource; this does not prove the
source enabled-SIE prologue or migration handling.

The public body WP takes the real generation certificate, packet, literal
frame and genuine continuation at Retire_Success. Its Link constructs
all register plans internally. It covers neither fetching/decoding nor
run_hart_active, clock/retirement/restart, source cap restoration or a full
push_off function. The native packet adapter follows MycpuKptRegister's
partition/fold/reassembly method generalized to arbitrary Regime; minimal
return and jump subplans can reuse existing checked building blocks.

Validation: `/tmp/xv6-lean-research/push-off-scalar-native.log` and
`push-off-scalar-audit.log`. The strict audit covers all 201 physical
origin declarations in six modules, including private lookup, all types,
opaque proof bodies and constructors. Only the three standard foundational
axioms occur; there are no unsafe/partial dependencies or exclusions.
The generated-body factor is kernel-checked reflexivity, followed by actual
native register plans. No runtime decision axiom or replacement model is used.
Concrete edge cases are recorded in `PushOffScalarChecks.lean` and
`push-off-scalar-checks.log`; source hashes are in
`push-off-scalar-source.sha256`, all under `/tmp/xv6-lean-research`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
