# Full Lean port: implementation plan

Status: initial design under independent review. This project is incomplete.

## Target and baseline

Port the full supporting development and closed whole-system theorems of
[arXiv:2609.04043v1](https://arxiv.org/abs/2609.04043v1) to Lean. Use the authors'
`arxiv-v1` tag, commit `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, rather than
silently mixing in post-paper changes. Pins live in `upstream.lock.json`.

The intended final statements concern the concrete kernel ELF and initial disk
image, all allowed CPU/device/power interleavings, and durable filesystem
consistency across repeated crashes. They must not assume function correctness,
initialization of all invariants, or a fresh disk on reboot. Quantify over arbitrary
user code supported by the configured architecture. Preserve TSO, sub-instruction
register and memory events, hardware page-table walks and A/D writeback,
interrupts, thread migration, DMA, out-of-order disk requests, and sector writes.

Preserve the paper's precise limits: safety, not liveness or noninterference;
TSO, not unrestricted RVWMO; the pinned Sail TLB and platform configuration;
resource-exhaustion panic paths may print and spin. Kernel integrity must not be
misreported as unconditional absence of all panic calls. Later upstream changes
are separate upgrades with explicit semantics and artifact comparisons.

## Architecture and exit gates

1. **Provenance and build.** Pin all sources/toolchains; recover literal kernel and
   fs.img bytes; reproducible generators, source inventory, CI and transitive
   axiom auditing. The entire artifact is inventoried, including inactive source
   files, but only the paper's active theorem dependency graph defines completion.
2. **Semantic interface.** Generate the paper's RISC-V model through a free-event
   Lean Sail V1 backend. Preserve dependent register types, complete memory
   requests/results, barriers and choices. The sequential V1 EStateM interpreter
   erases precisely the concurrency needed here and cannot serve as the model.
   Establish event correspondence and a sequential interpreter check before using
   instruction rules. Use the fixed atomic A/D model from the paper's Sail pin.
3. **Logic and machine.** Reuse native iris-lean's actual OFE/CMRA/UPred/IProp
   model and generic adequacy. Port production TSO memory, machine language,
   devices and power transitions. Instantiate the language and prove state
   interpretation, ownership rules and generic machine adequacy. Two pure Sail
   reservation predicates must be explicit fixed parameters; all effectful hooks
   require faithful definitions or documented unreachability obligations.
4. **First closed machine-code slice.** Decode actual bytes, execute real Sail
   events and discharge initialized resource and adequacy obligations for a small
   concurrent program. Include nontrivial interference and memory ordering. This
   is a feasibility gate, not a substitute for the xv6 theorem.
5. **Reusable kernel abstractions.** Port view-relative ownership, suspended
   views, instruction rules, address-translation tiers, interrupt capabilities,
   stack budgets, ABI and nonreturning stack reclamation, spinlocks/sleeplocks,
   boot allocation accounting, and context switches. Specs stay separate from
   implementations and proofs.
6. **Kernel subsystems.** Boot and allocator; page tables and arbitrary user-mode
   execution; process/scheduler/FD/pipe layers; UART/PLIC/virtio drivers and DMA;
   buffer and inode caches with reference escrow; journal and recovery with
   abstract durable disk state; filesystem invariants and syscalls. Keep the hard
   journal abstraction boundary: sector-level crash reasoning belongs below it.
7. **Whole-system closure.** Link every required function proof, discharge the
   concrete ELF/image initialization obligations, instantiate all invariants, and
   prove the pure filesystem and machine safety conclusions. Inspect complete
   transitive assumptions and theorem statements independently. Build success
   alone does not satisfy this gate.
8. **Conformance and maintenance.** Port paper conformance scenarios and captured
   results as checked executions. Record discrepancies instead of treating finite
   tests as universal hardware refinement. Measure proof build costs, and maintain
   reproducible symbol-relative regeneration for future kernel/model updates.

## Agent coordination

Follow paper §7: bounded tasks with owned files, named theorem contracts, explicit
exit criteria and dependencies; separate Spec/Code/Proof/Link files; no hand edits
to generated data. Review contract changes independently. Record assumptions,
failed designs, remaining obligations, exact checks and next tasks in shared
versioned documents. Start fresh agents at checkpoints where implicit assumptions
have become stale. Require early adequacy and initialization checks to expose
vacuity, especially duplicated ownership and crash-state resets. Profile when
build cost obstructs proof iteration.

The initial proposal is in `reviews/initial-proposal.md`. Claude Code was invoked
with model `claude-fable-5-1`, effort `max`, to read the full paper, contribute to
and critique the design. Its completed review and follow-up disposition will be
recorded under `reviews/`; an invocation alone is not recorded as approval.

## Current decisions and outstanding gates

- Native iris-lean is the preferred foundation; the available local Rocq/Lean
  importer goes in the opposite direction and is not a solution to this port.
- Align on the Iris dependency's Lean 4.32.2 after its build audit.
- Fork lean-sail for opt-in V1 free events; keep existing sequential semantics
  separate. Generator integration and full model generation remain unproven.
- Preserve paper model configuration and module list exactly, including modules
  needed for arbitrary user code even when the kernel does not use them.
- Raw image import is untrusted tooling. Lean decoding, ELF loading and filesystem
  initialization must eventually be checked, with correspondence to raw bytes.
- The upstream xv6iris snapshot has no repository license file. Preserve source
  references and notices; do not invent an upstream license or claim ownership of
  its artifact. Record provenance separately from proof completeness.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
