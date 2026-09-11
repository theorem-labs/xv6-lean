# Full Lean port: implementation plan

Status: Fable 5.1 max has completed six reviews; their required changes are tracked. This project is incomplete.

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
   is a feasibility gate, not a substitute for the xv6 theorem. The one-instruction
   JAL initialization/adequacy subgate is closed at `d6e1c89`; the inhabited two-hart TSO
   interference subgate is closed at `f252d3d` (see
   docs/reviews/fable-spinlock-gate-disposition.md).
5. **Reusable kernel abstractions.** Port view-relative ownership, suspended
   views, instruction rules, address-translation tiers, interrupt capabilities,
   stack budgets, ABI and nonreturning stack reclamation, spinlocks/sleeplocks,
   boot allocation accounting, and context switches. Specs stay separate from
   implementations and proofs.
   Current native prerequisites include partial supervisor PMP/interrupt WPs,
   value-agnostic optional clocks, ordinary context-word read/write event WPs,
   concrete supervisor checked eight-byte read/write WPs,
   physical stack rules, actual supervisor retirement and exact mycpu decode/fetch
   bytes plus nine native arithmetic-body rules. Bare translation and physical permission prefixes are proved; full
   page-table translation, virtual tier ownership and function composition remain open.
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

## Additional gates from Fable's design review

Before broad proof fanout, close generic device/power adequacy on a one-instruction
`jal x0, 0` image with the real configured machine, then close a two-hart spinlock
slice with nontrivial TSO interference. The first checks global initialization;
the second checks resource transfer and atomicity. Neither replaces the xv6 goal.

Keep reducibility in the exported safety conclusion. Enumerate and justify every
self-loop rule so a generic stutter cannot hide stuck hardware behavior. Prove a
concrete nonempty execution witness; prove that platform/initial-register
assumptions are satisfiable; and prove distinguishing filesystem lemmas accepting
the initial image and rejecting an invalid image. Add explicit crash-preservation
lemmas that retain the current durable disk instead of resetting it to fs.img.

Compute the active upstream theorem dependency closure, separate from the lexical
inventory. Reproduce the upstream assumption report in an isolated environment.
Report both the proof's axiom dependencies and the definitions reachable from its
statement. Generic adequacy alone is not a completed root: final audited roots
must instantiate the concrete filesystem and observable-trace predicates.

Measure kernel checking of image access and decoder facts before generating a
large instruction catalog. Packed 4096-byte numeric pages are the measured proof-access representation;
hex inputs remain available for extraction checks. The current facts establish
bounded input-byte observations and packed/list ELF parsing/loading correspondence;
full raw-encoding correspondence is now checked; complete filesystem initialization remains open. Generator
outputs must remain reproducible, with the Sail compiler revision and backend
options pinned alongside model sources.

The Sail/Rocq comparison has a specific remaining issue: the paper's Choose arm
resumes erased `ChooseNat`/`ChooseRange` values as arbitrary integers, whereas the
Lean interface retains natural/finite result types. A reachable-choice validity
proof or a compatible erased-choice treatment is required. Do not silently narrow
paper behaviors. Also relate optional write payloads, cycle count values, and
reservation hooks explicitly. Conformance replay provides evidence, not a proof
of this correspondence.

Intermediate boot or function linking theorems may expose explicit unproved
contracts as hypotheses. They remain visibly conditional and cannot satisfy a
closed milestone or be counted in completed whole-system coverage.

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
and critique the design. Both completed reviews and the coordinator disposition are recorded under
`reviews/`; their required changes remain explicit gates.

The language must be parametric in its boot image so the one-instruction gate and
the final paper-image theorem use the same machine semantics. See [exact theorem targets](THEOREM_TARGETS.md) and
[abstraction conventions](CONVENTIONS.md).

## Current decisions and outstanding gates

- Native iris-lean is the preferred foundation; the available local Rocq/Lean
  importer goes in the opposite direction and is not a solution to this port.
- Align on the Iris dependency's Lean 4.32.2 after its build audit.
- Fork lean-sail for opt-in V1 free events; keep existing sequential semantics
  separate. Full generation and compilation are complete, with explicit platform
  parameters and audited entry points; source semantic correspondence remains open.
- Preserve paper model configuration and module list exactly, including modules
  needed for arbitrary user code even when the kernel does not use them.
- Raw image import is untrusted tooling. Packed image access is kernel checked;
  whole-image correspondence and ELF loading are now checked, including raw hex
  decoding. Complete filesystem initialization remains open.
- The full pure initial `Snapshot.OK` is now proved against the pinned disk.
  Native byte/top/link assembly and initial `P_dur` allocation are also proved,
  with a literal initial-image leaf and an audited initialization-only caller
  policy. Full resource readback is now proved, retaining the exact snapshot
  while deriving all validity clauses. Source-instance transfer and cloning are now proved; crash
  preservation remains required. A fresh snapshot ghost does not reset disk.
- The second integration image has checked fetch/decoder and complete
  instruction plans, native lock callbacks, actual boot resource extraction
  and eight-way code sharing. Instruction-family preservation and all-schedule
  native safety, operational exclusion, unique actual event annotations and
  the inhabited interference witness are now proved. The final combined
  gate satisfies all requests from Fable's sixth review.
- The generic interruptible event fold and actual cycle wrapper are now
  checked. The native lock protocol transfers the counter resource only at
  successful conditional-write commit, retaining its actual winning log
  position. Concrete annotation updates are now functional, all selected-hart
  event cases and worker/power cases are proved, and the first actual conflict
  trace is checked. Other-hart framing, full concrete pool coverage, actual
  annotation existence and an inhabited holder checkpoint on the same final
  seven-message run are all proved. Supervisor kernel composition is next.
- The upstream xv6iris snapshot has no repository license file. Preserve source
  references and notices; do not invent an upstream license or claim ownership of
  its artifact. Record provenance separately from proof completeness.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
