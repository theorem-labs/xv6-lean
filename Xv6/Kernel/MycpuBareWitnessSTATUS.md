# Concrete actual-machine Bare mycpu witness

Nine new modules implement the operational inhabitation obligation requested
by the completed Fable round 7 review of MycpuBare. The witness starts at an
explicitly configured supervisor state. Reaching that state from the actual
kernel boot path, and allocating its native Iris entry resources, remain open.
The existing MycpuBare WP has neither been changed nor replaced by this run.

The initial image is exactly `loadedRam Xv6.Machine.bootImage`, including the
actual file-backed kernel bytes and all zero-filled remaining RAM. CPU 3 has
TP=3, SP=0x80040000, RA=0x80000100 and S0=0x123456789abcdef0. Its SATP mode is
Bare, PMA is pmaBoot, and TOR entry0 has R/W/X with upper address covering the
complete RAM interval. Both scratch words initially contain zero. Interrupt
enables are zero and SIE is false. The false optional-clock choice is taken
on each of fourteen actual `cycle` programs; this fixes a permitted execution
witness and does not restrict the machine relation or the general MycpuBare WP.

Definitions and proof roles:

- Defs/Spec define the concrete hardware state, total read cache, bounded
  write-pausing evaluator, compact checkpoints and eight public contracts.
- RunProofs proves EntryConfig, the total cache's equality to the actual image,
  soundness for every accepted evaluator event and restart composition.
  Existing pauseRun supplies actual register and ordinary RAM-read steps.
  Each write uses the retained actual request/continuation, modifies physical
  bytes, appends its full snapshot with author 3, clears the reservation and
  retains view 0. Unsupported events fail; no invented transitions are accepted.
- OrderProofs compares the pure register-update order generically outside the
  seven clock/retirement fields. FirstCertificates/LastCertificates check each
  complete generated state equation once, then prove full register equality
  using that bridge and explicit checks of the remaining seven fields. Every
  register and the full local state remain covered; the original generated
  execute is used through actual try_step.
- ResultProofs connects the expected final checkpoint to MycpuBare.Result and
  HartResult, proves initial/final stack contents and all 34 unchanged code
  bytes, and states the exact global frame. Final A0 is 0x80012568, RA/S0/SP
  are restored, minstret is 14, both optional-clock counters stay zero, view is
  zero, and the reservation is absent. The log contains exactly two stores.
- AssemblyProofs connects the fourteen checked equations to actual NodeSteps,
  real HartStep/writeBack and fixed-thread Iris PoolSteps, including positive
  step count and initial/final MemoryOK and ReservationsOK. Other hart files,
  all device state, the complete initial image, power, generation and other
  reservations remain intact.
- Proofs closes all eight public contracts with the concrete certificates.

Source mapping: pinned xv6iris arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, iris/CodeMycpu.v (all fourteen
instruction facts), iris/ProofMycpu.v (saved-register and result arithmetic),
iris/ProcGeom.v (CPU array address), and iris/RiscvLang.v (node/restart/hart
semantics). Actual compiled execution is the pinned generated Step.try_step
and complete dependency cone already used by the machine model. The read-cache
bridge reuses MycpuFetchBytes.ram_byte over all 34 bytes, including the two-byte
fetch spill into the following symbol; zero-RAM specialization uses the proved
ELF bootByte_after_file law. No whole-machine cross-backend equivalence is
inferred from this witness.

Validation: the complete target passed 733 jobs. The first seven generated
certificates compiled in 30 seconds and the last seven in 196 seconds; final
contract assembly compiled in 922ms. The fresh physical-origin audit passed
all 165 logical declarations in nine modules, including private helpers,
types, all opaque bodies and datatype constructors. Only
propext/Classical.choice/Quot.sound occur. It also checks the single
compiler-only `run._unsafe_rec` companion against its safe total owner; that
companion is absent from every logical dependency cone, matching the
repository's established runtime-companion policy. No initial-allocation,
unsafe or partial declaration occurs in the semantic dependency cone. No
sorry, native_decide, bv_decide or custom axiom is used.

Reproduction:

- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.MycpuBareWitnessProofs`
- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/MycpuBareWitnessOwnerAudit.lean`

Final evidence: /tmp/xv6-lean-research/mycpu-bare-witness-shared-build.log and
mycpu-bare-witness-owner-audit.log. The data-register comparison uses the
proved generic OrderProofs bridge; the remaining seven control fields are
explicitly kernel normalized in each certificate. This proves full register
and local-state equality, not merely equality modulo ignored fields.

Independent nine-module source review passed; Fable round eight approved
with no soundness blocker. Its pool wording request is discharged by the
separate tenth module MycpuBareWitnessPoolProofs: full_pool_positive proves
the same run in the actual twelve-thread power :: powerFork0 pool. All
other workers are present and unscheduled. Its five declarations passed
full coordinator dependency review and the target builds735 jobs. The
entry_ms_facts theorem checks all ten MsFacts of actual entry mstatus.

The witness chooses one Platform (both reservation predicates false),
Devices.initial, false optional-clock choices, minimal read views and a
synthetic configured state with seven other zero register files. Boot
reachability and native era-named bit/context/register/stack allocation
remain open. See docs/reviews/fable-mycpu-witness-disposition.md.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
