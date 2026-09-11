# Regime cycle shell: implemented and frozen

`pureSpec` proves all six pure contracts. `nativeSpec` and `registrySpec`
construct all five native contracts from the existing register, retirement,
clock, restart and bit-ownership rules. The active fetch/body WP remains an
explicitly conditional residual, not a completed kernel-function gate.

Owned files: `MycpuRegimeShell{Defs,Spec,Plan,Resources,Proofs,Link}.lean`
(six modules, 413 lines), this status, and
`docs/design/mycpu-regime-cycle-boundary.md`. Source pins and exact
correspondence appear in that design. Existing Bare and KPT modules are unchanged.

The ownership partition is 50 common physical keys, plus exactly three Bare
or four KPT translation cells. Native SIE/SRET fragments, full pinned GPRs,
x0, context, timer and virtual stack retain their explicit meanings. No new
camera or runtime allocation is added; full `sconf`/`strans_inv` is not claimed.

Validation command:
`PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.MycpuRegimeShellLink`.
GREEN: 885 jobs; native Proofs 1.1 s, Link 968 ms. The initial signature
checkpoint passed 554 jobs. Full physical-origin audit: all 149 declarations
across six modules, including private definitions, types, full opaque bodies
and constructor dependencies. Only `propext`, `Classical.choice`, and
`Quot.sound`; no unsafe or partial dependency, zero exclusions.

Exact native implementation entry points: `partition`, `disabled`, `wp_start`,
`wp_finish`, `wp_restart`, `actual`, `nativeSpec`, `registrySpec`. Register
plans use only the 18 control cells and retain every remaining resource as
a real frame. The public reversible 50-cell partition is also proved.

Audit/replay records live outside the repository:
`/tmp/xv6-lean-research/MycpuRegimeShellAudit.lean`,
`mycpu-regime-shell-audit.log`, and `mycpu-regime-shell-build.log`.

Independent final coordinator review passed: all six modules were read and
a fresh audit independently checked all 149 declarations with the same
standard-axiom result and zero exclusions. See
`docs/reviews/mycpu-regime-shell-peer-review.md`.

Next: concrete KPT fetch/body composition
and the source capability wrapper. The physical regime branches do not
allocate or imply the source translation publication one-shot or complete
hardware configuration. The suffix success constructor is an actual program
input; arbitrary instruction success is never assumed or proved here.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
