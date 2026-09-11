# Native supervisor eight-byte physical reads

Implemented and frozen for independent review in `SupervisorReadDefs`, `Spec`,
`Plan`, `Proofs`, and `Link`. The public `wp_checked_read` and `nativeSpec` prove
actual `checked_mem_read` at explicit Supervisor privilege, PBMT_PMA, width
eight and four false flags, for either ordinary data or page-table-entry load.

The caller supplies the real generation certificate, four independently
fractional register cells, a running context and its fractional exact eight-byte
word assertion. The pure configuration premises are the existing positive
entry-zero supervisor TOR grant, the mathematical RAM interval, disabled HTIF,
the actual matched PMA region and its relevant readable/PTE-read permission.
Alignment comes from the word assertion; it is not an additional public
precondition. The actual guarded continuation receives the same register,
context and word ownership and a lower-bound receipt for the chosen read view.

There is no caller-supplied read result, readability fact, memory-successor
preservation callback or subordinate access implementation. The concrete
TsoContextReadWP proof opens/restores the complete live era and derives the
result for every allowed actual read view from context ownership. It handles
arbitrary logs and views without imposing a top view or an empty log. Existing
generation/dead-thread rules handle power changes between prefix events.

`wp_checked_read_reservation` additionally frames and returns the same optional
reservation fragment. No exclusive snapshot is created or cleared; the actual
plain read changes only the selected view (`TsoContextReadWP.advance_frame`).

The pure `Boundary` has just an actual read-event constructor and an unchanged-
register `RegisterPlan.Returns` prefix constructor. `Boundary.fold` uses native
RegisterPlan.fold and the concrete native RAM rule. `checked_boundary` constructs
this decomposition from the generated code itself, including the singleton
loop, zero-offset arithmetic and full-width accumulator update. `OneRead`
retains every successful optional tag and the error response: success reduces
to `pure (Ok (word, ()))`; `.Err ()` reduces to the generated `Error.Exit`.
The native owned read actually supplies `.Ok (word, none)`.

The exact register sequence is PMA once, PMP configuration once, PMP
configuration again and PMP address in `pmpReadAddrReg`, then HTIF once. These
five reads use only four distinct fractional cells. The successful priority
wrapper does not perform an extra PMP check. The eager HTIF read is preserved.
Both access classes emit the actual `AK_explicit` plain/normal request, VA
none, the actual physical address, unit translation metadata, size eight and
tag false. The PTE class does not emit `AK_ttw` in this generated model.

Source mapping, pinned xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`:

| Lean result | Source / actual generated path |
| --- | --- |
| `checked_boundary` | `SmodePte.v:336–420`, the checked-read portion of `exec_read_pte_S`; actual `Mem.lean:404–458` |
| Singleton loop and alignment | Actual `SplitAccessUtils.lean:255–267`, `Mem.lean:221–237`, `is_aligned_paddr`; `add_zero` and `full_word` are ordinary kernel proofs for arbitrary inputs |
| Exact event and response tails | Actual `PhysMemInterface.lean:335–376`, `read_ram` |
| Native prefix staging | Existing partial-register `RegisterPlan.fold`; comparable source staging in `SmodeCorePt.v:1321–1530`, without claiming its separate fetch ownership contract |
| Owned RAM read and view receipt | Existing `TsoContextReadWP.wp_read`, registered context and full era/heap/TSO restoration |

The source `exec_read_pte_S` uses a raw byte-read premise and concludes a larger
`read_pte` wrapper execution. This slice instead discharges its checked-read
boundary through native exact context-word ownership. It does not yet port the
outer callback/metadata wrappers. In particular, a PTE-class checked read does
not establish the canonical A/D-set pin/publication credential bridge used by
`kpt_slot_pin` and `cv_boot_cred`: those permit A/D variants and require a
separate native walker proof. Virtual translation, pointer masking, effective
privilege, misaligned splitting, exclusive reads, MMIO, two/four-byte fetch,
instruction execution and whole-kernel correctness are outside this slice.

Validation:

- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.SupervisorReadLink`
  passed 514 jobs. Pure plan and native proof modules each took about 1.2 s.
- The physical-origin audit in `/tmp/xv6-lean-research/SupervisorReadAudit.lean`
  checks all declarations from all five modules, including private/generated
  declarations, types, opaque bodies and inductive constructors: all 109
  declarations passed (`supervisor-read-audit.log`). Only `propext`, `Classical.choice`
  and `Quot.sound` occur. There are no unsafe/partial semantic dependencies or
  excluded compiler runtime companions.
- Exact request, all response tails, arbitrary-word assembly and the public
  native rule are compiler-checked proofs. No new axiom, `sorry`, native
  decision tactic, generated-model edit, new camera slot or existing-file
  modification was required.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
