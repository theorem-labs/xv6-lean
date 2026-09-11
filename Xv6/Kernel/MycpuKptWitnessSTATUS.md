# Configured Sv39 mycpu operational witness: frozen

All ten modules compile in 738 jobs and close the sixteen unchanged,
coordinator-approved contracts. `actual : Spec` has no execution or native
resource premise. `cycles` counts fourteen actual generated cycles;
`operational` composes their real restart/node transitions; `full_pool`
proves positive execution in the actual twelve-thread power :: powerFork0
pool. All workers remain present, with only CPU3 scheduled.

The configured memory and TSO image overlay three complete page-table pages
at 0x80050000/51000/52000 on the actual loaded kernel RAM. All3*512 words
are proved byte-for-byte: root index2 and middle index0 point downward;
leaf index1 is code RX and index63 is stack RW, both with A=D=1; every other
entry is zero. SATP is mode8/ASID0/rootPPN0x80050. The first fetch performs
an actual three-level miss and fills code TLB index1; the first stack save
fills index63. Actual A/D logic makes no PTE write in this configured run.
The full final TLB, including all unchanged entries, is part of each full
register-file certificate.

CPU3 retains the published Bare witness's other concrete register values:
TP3, SP0x80040000, RA0x80000100, S0x123456789abcdef0, source misa and
menvcfg constants, supervisor privilege and disabled SIE. The platform fixes
both reservation predicates false; devices are Devices.initial; the other
seven hart files are zero. False optional-clock choices and read view0 are
one permitted execution choice, not a restriction on the machine relation.
The entry is explicitly synthetic/configured, not established by boot.

Proof roles:

- RunProofs proves the image-parameterized evaluator sound for arbitrary
  accepted programs, caches equal to actual images, writers and local
  states with the real view/log bound. It reuses frozen pauseRun_sound;
  present ordinary RAM writes retain actual requests and continuations,
  update bytes, append the exact author-tagged snapshot and clear the
  reservation. Unsupported events fail. No pause is treated as progress.
- ImageProofs proves the actual cache equality, all1536 table-word reads,
  initial zero scratch words, all34 preserved real kernel code bytes,
  all table bytes and arbitrary memory outside the two real stores.
  Initial MemoryOK includes the entire RAM domain and true image/log/cache
  agreement. Initial reservations are absent.
- CompactProofs proves a flat full register file equal to the original
  source-ordered checkpoint at every index0..14. It checks the changed
  projections and derives all others from the source reference's proved
  frame. It is expected-output bookkeeping, not an instruction evaluator.
- FirstCertificates/LastCertificates use those proved input/output
  equalities, evaluate the actual complete generated cycles and check every
  constructor of the dependent 180-register file plus every local-state
  field. There is no equality modulo ignored registers. The two shards
  compile in10s and11s; the compact bridge compiles in10s. This avoids
  repeated expansion of a nested source reference in every Sv39 read.
- ResultProofs restores all thirteen callee-saved registers and RA/SP/S0,
  returns PC/nextPC0x80000100 and A0x80012568, retains all source stable
  controls and Sv39 SATP, and checks minstret14 with mcycle/mtime0. The log
  contains exactly the two original RA/S0 saves. `Result` does not reuse
  Bare.Result, whose configuration requires Bare mode.
- AssemblyProofs/Proofs connect the actual cycles to selected-hart
  writeBack and full PoolSteps. All other hart files, the complete device
  state (including durable disk), initial image, power, generation, views
  and reservations are preserved. Final MemoryOK and ReservationsOK follow
  from the actual global run. Closed contract assembly compiles in814ms.

Fresh audit: all 222 physical declarations across all ten physical modules,
including private helpers, with exporting disabled and full type, opaque-body
(`allowOpaque := true`) and constructor traversal. Only propext,
Classical.choice and Quot.sound occur. The proof-only evaluator is explicitly
noncomputable: Lean emits no unsafe recursion companion. The audit checks
every physical declaration with zero exclusions, and no unsafe/partial
dependency occurs in any complete cone. No Initial-allocation dependency exists.
No sorry, custom axiom, native_decide or bv_decide is used.

Reproduction:

- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.MycpuKptWitnessProofs`
- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/MycpuKptWitnessOwnerAudit.lean`

Evidence is mycpu-kpt-witness-final-build.log and
mycpu-kpt-witness-owner-audit.log under /tmp/xv6-lean-research. Four additional
ordinary-kernel checks confirm Sv39 mode, exact distinct TLB indices1/63
and both concrete entries (MycpuKptTlbChecks.lean and its log).

Source mapping: paper pin fa7f0a01c4b40489fac8ad303f079c2dfc7a1476,
CodeMycpu.v/ProofMycpu.v for all fourteen instructions and register results,
RiscvLang.v for node/restart/hart transitions, and generated
LeanPaperStock Step/Vmem/VmemTlb for the executed Sv39 paths. The actual
kernel bytes use the proved MycpuFetchBytes bridge and original ELF-loaded
RAM fallback. See docs/design/mycpu-kpt-witness-boundary.md.

Native SConf/KPT/resource inhabitation, construction/publication and
SATP-switch boot reachability, the translated native function WP,
cross-prover correspondence and all six whole-system theorem roots remain
separate open obligations. This is one configured operational witness,
not an all-schedule safety or whole-xv6 theorem. No existing generated,
published Bare, ownership, umbrella or other-owner file was modified.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
