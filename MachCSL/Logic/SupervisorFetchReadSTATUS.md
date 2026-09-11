# Native two- and four-byte supervisor physical fetch reads

SupervisorFetchRead{Defs,Spec,Plan,Proofs,Link} is implemented and frozen for
independent review. `wp_checked_fetch` proves the native WP for actual
`checked_mem_read (InstructionFetch ()) PBMT_PMA Supervisor (Physaddr address)
n false false false false`, restricted exactly to n=2 or n=4. `wp_fetch2` and
`wp_fetch4` expose BitVec16 and BitVec32 specializations. The public resource
contract is implemented by `nativeSpec`, with no subordinate access or
state-preservation implementation premise.

The owned resource is the new alignment-free TsoContextBytes window at the
exact physical address and width, together with a real running context and
generation certificate. Four independently fractional register cells hold
PMA regions, PMP configurations, PMP addresses and HTIF base. Pure assumptions
are actual two/four-byte physical alignment, positive source-supervisor TorRam
configuration, the mathematical RAM interval, HTIF none, the actual matched
PMA region and its executable permission. No eight-byte alignment, enclosing
word, empty log, immutable image, reset register file or selected read view is
assumed. The existing TorRam package includes R/W as well as X; this path
consumes its instruction-fetch grant.

The exact generated prefix performs five reads: PMA once, PMP configuration
then configuration/address inside pmpReadAddrReg, then eager HTIF. PMA success
returns CannotSplit; its priority wrapper performs no additional PMP check.
The singleton loop retains its dummy assertion, offset-zero address addition,
actual PMP/MMIO checks and full 16/32-bit accumulator update. Independent
ordinary kernel proofs establish those updates for arbitrary returned words.
The two concrete width proofs share the generic Boundary and composition laws;
they do not evaluate at one boot register snapshot.

Although the access class checked by PMA/PMP is InstructionFetch, all three
read flags are false, so the actual RAM read kind is Read_plain. The real V1
request remains explicit plain/normal, VA none, actual PA, unit translation,
size n and tag false. `checked_boundary` retains the full residual: every
successful word/optional-tag response returns `Ok (word, ())`, and `.Err ()`
produces the generated Error.Exit. These tails are proved from the code, not
supplied by the caller.

`Boundary.fold` uses the actual native RegisterPlan prefix fold and
TsoContextBytesReadWP.wp_read. The latter opens/restores the complete live era,
including heap metadata and all TSO resources, derives the same word at every
allowed view and pays the actual read view advancement. The final guarded
continuation receives the original register shares, context/window and a
receipt for the chosen view. Generation/dead-thread handling remains actual.
`wp_fetch_reservation` frames and returns the same arbitrary optional
reservation: this plain read neither creates nor clears a snapshot.

Source pin: xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

| Source / actual generated path | Implemented boundary |
| --- | --- |
| `SmodeCorePt.v:1321ff` hfrun_check_pma_ifetch_S | Existing SupervisorPhysical priority_aligned_plan with exact fetch2/fetch4 support and executable grant |
| `SmodeCorePt.v:1350ff` swp_checked_mem_read_ifetch4_S; `:1457ff` corresponding ifetch2 section | Actual checked_boundary and concrete native wp_fetch4/wp_fetch2 with internally paid context-window read |
| `Mem.lean:404–458`, SplitAccessUtils.split_misaligned | Exact single-iteration checked read and generated early-return handling |
| `PhysMemInterface.lean:335–376` read_ram | Real Read_plain V1 event, optional tag ignored, error Exit retained |
| Source fobl_ram callback | Discharged internally by actual context byte ownership; no public readability oracle |

The source's text ownership is richer than this physical context window:
RiscvPtsto.text_pointsto additionally carries a virtual mapping, positive
canonicality, text-address/tier pins and pristine ownership. No translation or
text ghost assertion is inferred from an ELF byte certificate here. The
existing mycpu certificates establish a 34-byte initial fetch footprint,
including two bytes after its 32-byte body. Its overlapping fourteen windows
still require extraction of the unique span once and exact reassembly, or
legitimate persistence before duplication. This module performs no concrete
boot allocation.

Actual fetch_bytes/fetch still include virtual translation, effective-
privilege reads and fetch dispatch. The four-byte aligned fast path requires
Ziccif enabled (already independently certified for the pinned model);
uncompressed instructions on a two-byte-only-aligned path require a second
translated fetch. Those stages, the KPT/tier/pristine bridge, complete native
mycpu fetch, decode/execute composition and whole-kernel correctness remain
separate. The primitive rule makes no broader all-memory identity claim.

Validation: `tools/lake.py build MachCSL.Logic.SupervisorFetchReadLink` passed
509 jobs; Plan about 1.1 s, native proofs 953 ms and final Link 950 ms.
The fresh `/tmp/xv6-lean-research/SupervisorFetchReadAudit.lean` checks every
physical-origin declaration in all five modules, including private width
proofs, types, opaque bodies and inductive constructors. All 89 declarations
passed with only propext, Classical.choice and Quot.sound, zero exclusions and
no unsafe/partial semantic dependencies (`supervisor-fetch-read-audit.log`). No camera slot, generated model change,
prior-owner edit, custom axiom, sorry or native decision tactic was used.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
