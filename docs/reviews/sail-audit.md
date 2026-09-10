# Sail / Lean dependency audit and implementation checkpoint

Status: the opt-in event library and its tests compile; full RISC-V model generation,
Rocq correspondence, SoC integration and adequacy are not yet established.

## Exact baseline

- Read all 47 pages of arXiv:2609.04043v1, including orchestration section 7.
- Paper artifact: mit-pdos/xv6iris arxiv-v1, fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.
- Paper Sail: zeldovich/sail-riscv 23dcf8fd923eb8a1958795393d2975632aa940b2.
- Current artifact Sail: 070832a1e4b086f0c6f7635de54cc2b4cfd66993. Only 7 changed lines
  distinguish it from the paper model: AK_ifetch/AK_ttw classification in memory events.
  This observability change must be an explicit subsequent upgrade.
- Existing /data/jason/sail-riscv remained untouched, clean at
  a031078002842b8ecc35b96f6961a3ceba2ceec4, origin theorem-labs/sail-riscv.
  Its model/sys/vmem.sail still uses blind A/D writeback and must not be the baseline.
- lean-sail v5: 079463134b9c50450b8393e1566a09fc492a34d9.
- Upstream Sail inspected: 5745ea9e5369ab4fc51de6f8b773dd8ebc323357.
- Iris current: 728a17140939e49af9236f7cb0d037da9ec52435; Lean 4.32.2.
  A separate agent owns the Iris completeness audit.

## Failure of the stock Lean route

Sail/ConcurrencyInterfaceV1.lean:109 defines PreSailM as EStateM. Register
operations manipulate sequential state; memory calls interpret requests immediately;
barriers and translation/trap/TLB/cache events are erased. Generated monads use a
trivial deterministic choice source. This does not express sub-instruction interleaving,
TSO fences, asynchronously delivered interrupts, or the full initialization choices.

Sail/ArchSem.lean already has FreeM with resumable effects but is a different interface.
The paper model constructs V1 requests, including conditional-write Option Bool results.
Merely defining CONCURRENCY_INTERFACE_V2 is not a valid conversion.

## Implemented opt-in library

Isolated clone: /tmp/xv6-lean-research/lean-sail-free-v1, initially lean-sail v5.
Files:
- Sail/ConcurrencyInterfaceV1Free.lean
- SailTest/ConcurrencyInterfaceV1Free.lean
- lean-toolchain (4.32.2)

The original sequential V1 file is unchanged. The free interface imports the original
request and architecture types, and uses the existing ArchSem FreeM implementation.
Each event retains its dependent response type. Memory requests retain every field:
access_kind, optional VA, PA, translation summary, dynamic size, tag, optional payload.
Memory writes return Result (Option Bool) abort, without forcing success or ruling out
failure/absence/abort. Register operations preserve the dependent register type.
Barriers/cache/TLB/translation/traps/clock/printing are explicit events. Choice uses
primitive response types and never runs a deterministic ChoiceSource. Empty-response
errors are distinguishable from explicit discard. Early return uses ExceptT, and
catching user exceptions preserves all prior events.

The free monad deliberately has no ChoiceSource argument: retaining an ignored phantom
argument caused unresolved inference metavariables and misrepresented the semantics.
Generator aliases therefore require an explicit opt-in change.

undefined_range uses inclusive finite choice, with unreachable on reversed bounds;
this follows Sail's inclusive range contract, not sequential V1's modulo high-low bug.
unwrapValue requires IsPure computation evidence: True for immediate .pure and False
for every event. Generator glue must provide a proof that concrete constants reduce to
.pure. Both impure Nat and impure Unit extraction are negative compile tests. A previous
Unit-fallback design was rejected during review because it could erase Unit-valued effects.

## Validation

/data/jason/.elan/bin/lake build succeeds on Lean 4.32.2, including original library
and tests and new tests (15 jobs at this checkpoint). New checked tests demonstrate:

- both true and false responses to an undefined Bool;
- request metadata preservation, including optional virtual address;
- successful and failed conditional writes, no exclusive result, and architectural abort;
- a tagged tablewalk read at its dependent 32-bit width;
- a fence remains before its following write and cannot be erased;
- an explicit two-thread schedule: read 0; other thread writes 1; read 1;
- dependent register types Nat and Bool;
- assertion/exit computations have no successful trace;
- early return/user exception handling retains preceding effects;
- singleton and both endpoints of inclusive range choice;
- impure Nat and Unit constant extraction is rejected (#check_failure);
- early-return coercions preserve the event prefix.

Checked representative theorem axioms are only propext. No custom axioms, sorry,
unsafe declarations, or partial definitions were introduced. These are interface tests,
not RISC-V verification or a validated SoC semantics. The test-specific register handler
is deliberately confined to the test file.

## Model and proof obligations remaining

1. Generate the exact paper Sail model using its config and module list. Never trim
   enabled instructions based merely on those occurring in the kernel: arbitrary user
   execution must consider the entire configured decode image.
2. Finish opt-in generator aliases/imports/specialization and compile actual output.
3. Preserve the paper's atomic A/D update: exclusive reread, fresh leaf validation,
   conditional write. Do not replace it with a blind write.
4. Prove a correspondence with the paper's Rocq free-event interface. Type differences
   include integer versus natural counters, optional write announcements, explicit
   register access-kind fields, and how undefined-range constraints are represented.
5. Define the paper's SoC event-handling relation: TSO timestamps and write histories,
   exclusive access protocol, devices/MMIO, DMA, interrupt wires, and power cycles.
   The event library deliberately does not decide valid read values or atomicity.
6. Retain disk state across reboot. Closing device/boot/invariant allocation adequacy
   is required; a theorem quantified over an impossible invariant is not completion.
7. Port hooks explicitly. The paper realizes load/cancel reservation and terminal output
   as no-ops, and leaves two fixed pure reservation predicates. Parameterize these and
   quantify over them, instead of silently choosing SC-always-fails. Pure predicates
   cannot be described as dynamic reservation state. Other external hooks need proofs
   of unreachability or explicit implementation; executable extras contain panic stubs.

## Compiler availability

No Sail was installed on the normal PATH. An isolated source clone at
/tmp/xv6-lean-research/sail-free-v1 was checked out at release 0.20.2. Its tag object
4a2c47e94ee88f6eb3e87ac94fe4604808778e36 peels to the actual release source commit
(shown by git rev-parse HEAD). Building against the existing 4.14.2 switch failed
because menhirLib and lem were unavailable and sail_maker must also be included.
No shared opam switch was mutated. A published 0.20.2 binary tarball was subsequently
retrieved to /tmp/xv6-lean-research/sail-binary to investigate generation without
changing shared toolchains.

Primary upstream release documentation:
https://github.com/rems-project/sail/releases/tag/0.20.2-binary

## Agent management derived from the paper

Do not dispatch hundreds of leaf proofs until the event and adequacy interfaces are
accepted. Keep Spec/Code/Proof/Link separate; assign ownership by file; review abstractions
and ghost-state ownership before allowing implementation. Work in independent clones.
Record incompatible approaches and blockers prominently. Fresh agents should re-audit
status rather than inherit assumptions indefinitely. Progress means closed dependency
paths toward the actual pure top theorem, not accumulating unconnected lemmas.

Independent review: artifact_audit recompiled the library and found no current slice-level
soundness blocker; requested early-return CoeT support and exact 64-bit test address
carrier. Both were implemented and the full build passed again. Root review caught
the impure Unit unwrap issue; it was fixed with explicit computational-purity evidence.

Source 0.20.2 tag peels to 3b7af38d66466ecadad563158b07ce2f82fe05da. The official
binary runs with its own bin directory on PATH (including z3). A full paper model
stock-generation attempt is running, with exact args in sail-generation-args.json and
output in sail-generation.log. It does not yet use the free interface.

## Checked generator signature checkpoint

Separate worktree /tmp/xv6-lean-research/lean-sail-generator-prototype, branch
free-v1-generator-prototype, contains a current-backend specialization template and
a compiled generated-layout fixture. Full lake build succeeds (18 jobs). The template
is instantiated by literal placeholder replacement and checks model monad aliases,
dependent register/memory wrappers, early returns, pure constant extraction, and
negative checks for impure Nat and Unit extraction. See prototype/README.md.
No compiler patch or full RISC-V output is validated by this signature fixture.

The free library checkpoint published by root is 4cb7fe0eade622c5ce434b4e9ef8f7d0c509ab6f.
An initial documentation sentence incorrectly inferred BSD licensing from Sail; the
checkpoint corrects it: upstream lean-sail v5 has no tracked standalone LICENSE file.
No terms were assigned to inherited code.

New correspondence concern: coq-sail src/Values.v:646 maps ChooseNat and ChooseRange
to unbounded Z, with choose_prop bounds separate. Paper RiscvLang.v:941 existentially
resumes any choice and does not enforce those bounds. Native Lean Nat and bounded
finite range choices need a reachable-choice validity argument or explicitly broader
semantics before a literal trace-inclusion claim. The paper GetCycleCount handler
always returns 0%Z, so relating it to Nat 0 is straightforward.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
