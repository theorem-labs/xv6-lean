# Context-free pinned reads

Frozen `TsoPinnedRead{Defs,Spec,Pure,Proofs,Link}.lean` implements the first
native KPT publication-read prerequisite from xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. This is a resource-derived read
fact, not yet a native PTE-event WP, canonical PTE assembler, full shared
page-table invariant, or Sv39 translation theorem.

The capacity and names are exactly `Tso.Interp.Capacity` and `EraNames`.
Physical pins remain the existing `Tso.physLedgerPin` over the real byte
slot 0 and timestamp slot 1. All existing timestamp payload definitions
remain unchanged. History and view receipts use the existing capacities;
no new camera, runtime name, allocation, or authority copy is introduced.
`nativeSpec` instantiates the constructed `ReadSpec` at the existing
`FsBlockGhost.eraCapacity.tso` capacity.

| Exact source | Checked Lean counterpart |
|---|---|
| `CtxValues.cv_own:295–300` | `ownAnchor`, `ownAnchor_intro`, `ownAnchor_valid` |
| `CtxValues.cv_boot_cred:375–395` and introductions | `bootCredential`, `bootCredential_view`, `bootCredential_boot` |
| `TsoCtx.ledger_read_pin_ok:5332–5350` | `pin_valid`, `view_bound`, `receipt_read` |
| `TsoMemPa.pin_ok_author:2343–2370` | `visible_raise_above`, `readDown_raise_anchor`, `pinOK_author` |
| `CtxValues.cv_own_read:323–348` | `author_read` |
| `CtxValues.cv_slot_read_ok:426–486` | `slotAnchor`, `slotBytes`, `slot_read`, `slot_read_preserve` |
| Eight-byte specialization | `slotWord`, `word_read` |

The boot credential has both source arms: this CPU's view receipt, or
`hartAgent cpu = 0` and the publication log receipt. Each byte independently
retains its own floor below the common publication bound, its timestamp,
allowed set and one of the three source anchors: floor zero, an actual
byte-writing message authored by Nat agent zero, or that agent's view
receipt. CPU-to-agent conversion is explicit. No context ownership or
claim that all readers already have a high view is added.

The pure proof uses an equivalent decomposition of the source descending
scan argument: raising a read view to an already-visible anchor cannot
change the result, since only older messages become newly visible and the
scan stops no later than the anchor. Applying `PinOK` at that raised view
then constrains the actual original-view result. The native author proof
obtains the anchor from `History.logElem` and the exact `LogRep` in the
machine TSO interpretation. It does not assume a forwarding result.

`slot_read_preserve` returns the entire TSO authority, publication credential,
and all original fractional pinned cells. Full gen_heap metadata is an
untouched frame; this projection does not consume or recreate it. Read facts
cover every permitted view and every selected modular address with arbitrary
window length. No word alignment or no-wrap condition is needed for these
per-byte facts. PTE canonical assembly and store injection will impose their
own exact source geometry later. A permitted observed leaf byte need not
equal the currently owned physical byte.

Validation: `python3 tools/lake.py build MachCSL.Logic.TsoPinnedReadLink`
passed **501 jobs**; Pure built in 406 ms, final native Proofs in 1.0 s and
Link in 914 ms. The initial proof-mode disjunction syntax/unfolding and
implicit-argument errors were corrected before this successful build.
Fresh physical-origin audit checked **55 declarations in all five modules**,
including types, private declarations, opaque bodies with explicit
`allowOpaque := true`, and constructor dependencies. All cones use only
the permitted standard axioms; no unsafe/partial dependency and **zero
exclusions**. No custom axiom, `sorry`, native decision tactic, or generated
model/dependency edit was used.

Evidence: `/tmp/xv6-lean-research/TsoPinnedReadAudit.lean`,
`tso-pinned-read-build.log`, `tso-pinned-read-audit.log`, and
`tso-pinned-read-initial.log`. The broader proposed source KPT path remains
in `docs/design/supervisor-kpt-boundary.md`; pinned stores and actual
conditional PTE events are separate subsequent checkpoints.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
