# Native HartTp ownership and read correspondence

All five modules (Defs, Spec, Pure, Proofs, Link) are frozen. `pureSpec`
constructs all twelve representation laws; `actual` constructs all nine
native ownership laws from the register specification. `nativeSpec`
discharges that dependency with the actual existing register implementation.
No new registry slot, physical register allocation, CPU migration theorem
or function adapter is claimed.

The source is the complete `HartTp.v` and `WpGpr.v:98–136` at xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The software map is a total
function on five-bit GPR indices. Physical mapping explicitly names each
actual generated register and supplies its dependent type equality. Index
zero has no physical cell; its assertion is the exact zero-value fact.
The owned file folds over all 32 indices. The proved enumeration is
complete and Nodup; its physical keys are injective, Nodup and number 31.
No register-constructor arithmetic or unchecked cast is used.

`read_program` proves equality of the actual generated `rX_bits` free tree
with the typed read form for every five-bit index. It uses exhaustive
kernel reflexivity on the complete finite index enumeration; its conclusion
preserves the real register-read event and all results, rather than merely
an evaluated returned value. Closed finite map facts use ordinary checked
`decide`, never native_decide or bv_decide.

`lookup_split` uses a proved permutation of the complete key list to
extract one cell and its explicit filtered remainder. `remainder_set`
proves replacement changes no other indexed assertion; `replace`, `lookup`
and `update` restore the complete file. This remains exact for x0: a
replacement must supply the zero-value assertion. `zero_value` also reads
that fact from full file ownership.

The pin overrides TP with the current hart ID and leaves all other software
entries unchanged. `pinned_tp`, `read_other`, `hart_independent`, `pin_id`
and `pin_set` prove the source pure laws. `pinned_lookup` and
`pinned_update` transport the actual native resources; the latter excludes
TP exactly as required. `tp_accessor` returns the full actual x4 fragment
with its restoration wand. `actual_tp` combines that fragment with the
actual register interpretation to prove physical x4 equals the hart ID.
The pure pin definition alone is never treated as physical register truth.

All resources use the existing native register camera. No proof assumes
a full 180-cell physical file, selected execution or callee WP. No resource
transport between harts is asserted, and TP is not added to the ABI saved
set. The raw map update remains available to boot/trampoline proofs that
legitimately write TP. Full mycpu footprint composition remains a separate
step which must retain exact remainder ownership and avoid duplication.
The generated write callback is not analyzed by this read/resource slice.

Validation: `python3 tools/lake.py build Xv6.Kernel.HartTpLink` passed
349 jobs (Pure 1.5s, Proofs 1.1s, Link 824ms). The fresh physical-origin
audit checked all 155 declarations in all five modules, their types,
opaque bodies with allowOpaque=true and inductive constructors. Only
propext, Classical.choice and Quot.sound occur; no unsafe/partial logical
dependency and zero exclusions. Evidence:
`/tmp/xv6-lean-research/HartTpAudit.lean`, `hart-tp-build.log`,
`hart-tp-audit.log` and `hart-tp-frozen.sha256`.

The scope and next nonduplicating function adapter are described in
`docs/design/supervisor-capabilities-boundary.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
