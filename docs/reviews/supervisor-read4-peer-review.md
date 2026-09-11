# Supervisor four-byte read: independent review

PASS for the native physical ordinary-load scope. Codex independently
read all five coordinator-authored SupervisorRead4 modules, the generic
SupervisorFetchRead boundary/fold, the context-byte read implementation,
and the actual generated memory/PMA/PMP/read-ram paths. No correction or
production-file edit was required.

The program is exactly checked_mem_read Load.Data PBMT_PMA Supervisor
address4 with aq,rl,res,meta all false. Sharing the generic boundary with
fetch does not change its access class: the PMA prefix uses
SupervisorDataPma.load/readable, and the actual per-chunk pmpCheck uses
Load.Data and SupervisorPmp.Supported.load. No executable permission or
ifetch request is substituted. Actual matched-region, alignment, TOR RAM
coverage and disabled HTIF premises remain explicit; the theorem does
not manufacture general source Sconf or physical-address translation.

The footprint has precisely four independently supplied fractions:
pma_regions,pmpcfg_n,pmpaddr_n,htif_tohost_base. The generated successful
prefix performs five reads in order: PMA, PMP config, PMP config again
inside its address reader, PMP addresses, then HTIF. Its finite plans
preserve the entire register file, and the native fold checks footprint
uniqueness. The successful PMA-priority prefix makes no earlier PMP read.
PMP's first TOR entry grants the actual load; arbitrary later entries and
unconsumed register fields are retained by the existing proof.

checked_boundary unfolds actual Mem.lean:404–451, resolving the aligned
split to one four-byte chunk, retaining the loop assertion, and selecting
read_kind_of_flags(false,false,false)=Read_plain. Address+0 normalization
preserves the actual address. within_mmio_readable follows its real eager
CLINT/signature/HTIF checks; RAM range and disabled HTIF discharge MMIO.
The final request is exactly AK_explicit(AV_plain,AS_normal), va=None,
pa=address, translation=(), size4 and tag=false. The aliases reused from
SupervisorFetchRead happen to have this exact plain metadata; they are
not treated as instruction-fetch semantics.

The imported read_ram_boundary retains the complete V1 response tail:
every Ok(word,tag) becomes the same word with unit metadata; Err() is the
generated Exit, not an invented checked-read error result. The OneRead
bind/prefix proofs preserve that error through all wrappers. The singleton
32-bit assembly updates bits31..0 of the actual zero buffer; full_word
proves it equals the read word, rather than truncating or sign-extending it.
This is a32-bit physical read result; later LW sign extension is separate.

The native rule invokes the actual Boundary.fold and
TsoContextBytesReadWP.wp_read. The latter opens the full real era heap and
TSO interpretation and derives all-view readability from the running
context plus four fractional byte/timestamp resources. It restores the
interpretation before the event and handles every actual ordinary-read
successor. No supplied readability, selected-view, current-memory value,
returned-word or preservation oracle occurs. The public continuation has
exactly one later and universally quantified actual view receipt. It
receives the same four register cells, running context, word window and
fraction. No timestamp-fraction upgrade or log-empty assumption is added.

The chosen successor changes only the relevant view; the imported
advance_frame also proves memory, log, registers and reservations unchanged.
The public Spec does not consume or explicitly return a reservation token;
such tokens can remain in an ordinary Iris frame. The rule retains all
response tails in its structural theorem while native context ownership
justifies success, so ignoring the separately returned error equality in
wp_checked_read does not erase an operational error branch.

Source mapping: actual LeanPaperStock Mem.lean:221–237,262–382,393–451;
Pma.lean:349–416; PhysMemInterface.lean:335–370. The aligned PMA argument
matches iris/RiscvExtras.v:1015–1127 and its ordinary Load.Data applicability
rule. This review does not assert a full source virtual word4 or instruction
WP: those additionally require translation/capability/register-result
bridges. Source pin fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.

Independent verification:

- Build MachCSL.Logic.SupervisorRead4Link:517 jobs, success.
- Strict audit:34 physical declarations from all five modules, including
  private/generated declarations. Exporting disabled; per-root axiom
  collection and complete type, opaque-body (allowOpaque=true), constructor
  traversal. Only propext,Classical.choice,Quot.sound; no unsafe/partial
  dependency and zero exclusions.
- Driver /tmp/xv6-lean-research/SupervisorRead4PeerAudit.lean; logs
  supervisor-read4-peer-{build,audit}.log in the same directory.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
