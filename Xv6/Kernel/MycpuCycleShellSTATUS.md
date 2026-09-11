# Actual setup, retirement, clocks and restart on the common bundle

Frozen four modules: MycpuCycleShell Defs/Spec/Proofs/Link. `cycle_factor`
retains the actual setup, hart-state read, waiting and active branches,
postlude and optional clock. Under explicit actual HART_ACTIVE,
`start_prefix` and native `wp_start` reach actual run_hart_active with the
correct minstret flag, retaining the common28-cell bundle.

`wp_finish` applies successful real postlude and both permitted clock
choices, preserving all off-clock state relative to the actual retirement
post-state. `completed_pc` establishes both PC and nextPC equal the input
nextPC. `completed_other` frames every register outside PC/counter/clocks.
`wp_finish_restart` composes the real restart transition, consumes the
original reservation fragment and returns none, with a guarded continuation
for both next-cycle tick choices. No register or reservation is allocated.
Caller context/memory can be framed through these ordinary native CPS rules.

The active-body WP in the start rule remains an explicit residual-program
composition obligation. This is not a complete fetched-cycle or function
correctness theorem. Source program definitions are Machine.Node.cycle,
generated try_step/postlude and the independently proved native retirement
and restart rules. No failed/trap branch is removed from the factor.

Build: `python3 tools/lake.py build Xv6.Kernel.MycpuCycleShellLink`, 662 jobs,
final version without warnings. Full owner physical-origin audit: all34
logical declarations, opaque values/types/constructors, standard three
axioms only, no exclusions or unsafe/partial logical cone. Evidence:
/tmp/xv6-lean-research/MycpuCycleShellOwnerAudit.lean and
mycpu-cycle-shell-{build,audit}.log.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
