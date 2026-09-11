# Independent review: native supervisor physical read

Reviewer: the Codex Lean-logic agent, independent of the artifact agent who
implemented this slice. Result: **PASS for the declared physical checked-read
scope**; no code correction requested.

I read all five frozen `SupervisorRead{Defs,Spec,Plan,Proofs,Link}.lean` modules
and STATUS, the reused physical/PMP plans and context-read native rule, and
compared them with pinned xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, particularly
`SmodePte.v:336–415`. The generated implementation checked is the repository's
pinned `LeanPaperStock/Mem.lean:404–456` and
`PhysMemInterface.lean:335–370`.

The concrete program is the actual eight-byte `checked_mem_read` with explicit
Supervisor privilege, PBMT_PMA, and four false flags. Both ordinary data and
PTE-class loads are covered. The assumptions expose the real matched PMA
region and its appropriate permission, positive entry-zero TOR RAM grant,
RAM interval, and disabled HTIF. Alignment is derived from the context word
assertion. There is no caller-provided byte-read fact, subordinate access WP,
software contract, or state-preservation callback.

The constructed `checked_boundary` preserves the generated PMA-first priority
check, singleton split loop, PMP check, MMIO decision, and actual RAM event.
The exact register reads are PMA, PMP configuration, PMP configuration again,
PMP address, and HTIF. Only those four distinct cells are owned, with separate
arbitrary fractions; no whole-register-file resource is required. The eager
HTIF read is retained. The plain event has the actual explicit/normal access
kind, no virtual address, the supplied physical address, unit translation,
size eight, and false tag flag. The PTE-class branch uses this same event
rather than silently substituting a translation-walk event.

`OneRead` keeps the full residual for every successful word and optional tag,
and for the error response. Its append proof retains the empty-result error
event; it does not discard an executable error branch. The final accumulator
update is proved for arbitrary 64-bit words. Native ownership rules establish
success with tag `none`, after which the generated tail returns
`Ok (word, ())`; the other error residual is correctly the generated Exit.

`Boundary.fold` composes the existing native partial-register fold with
`TsoContextReadWP.wp_read`. Every real register/read event remains a separate
machine step. The latter opens and restores the live era's full heap metadata
and TSO interpretation and derives readability for every permitted selected
view from running-context and word ownership. The selected view receipt,
unchanged fractional word, context, and register cells reach the guarded
continuation. Generation/dead-thread handling remains that of the actual
native WP rules. The reservation corollary frames and returns exactly the
same optional fragment; it performs no exclusive acquisition or clearing.

The source `exec_read_pte_S` includes the outer `read_pte`/metadata wrappers
and uses an executable byte-read premise. This implementation establishes
the checked-read portion through native context ownership. It does not claim
those outer wrappers, effective privilege, translation, conditional A/D
updates, canonical PTE pins, publication credentials, fetch, or a complete
kernel function WP. In particular this exact-word physical read is not a
substitute for the separate `kpt_slot_pin`/`cv_boot_cred` A/D-variant bridge.
Whole generated-model/Rocq correspondence remains a separate project limit.

Validation: a fresh physical-origin audit covered all **109 declarations**
from the five modules, including private helpers. It traversed declaration
types, bodies with `allowOpaque := true`, and inductive constructors, and
checked transitive axioms. Only `propext`, `Classical.choice`, and `Quot.sound`
occur; no unsafe/partial logical dependency and no excluded runtime companion
were found. The script and output are
`/tmp/xv6-lean-research/SupervisorReadPeerAudit.lean` and
`supervisor-read-peer-audit.log`. A separate target rebuild passed **514 jobs**, recorded in
`supervisor-read-peer-build.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
