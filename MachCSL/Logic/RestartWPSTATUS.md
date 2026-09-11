# Actual hart restart rule

`RestartWP{Defs,Spec,Proofs,Link}` ports `RiscvExec.v:1007` over the actual
pure Sail hart node. This node is not a native language value: its next step
chooses either clock flag, clears only that hart's reservation, and begins the
actual generated fetch/execute cycle.

`restart_successors` inverts every live machine step and retains both possible
clock choices. `era_clear` consumes the real per-hart reservation fragment,
updates the full authoritative mirror, and proves ReservationsOK after clearing.
`power_clear` preserves fixed generation/start counters, durable disk custody,
era registration, all registers, RAM, devices and the complete TSO state. In
particular an instruction boundary neither drains the TSO log nor advances views.

`wp_restart` consumes existential reservation custody and a guarded continuation
for every tick value, returning actual native NotStuck WP. The source-shaped
`wp_restart_fragment` takes any explicit old reservation and returns none to the
continuation. Stale generations use the actual dead stutter and proved guarded
WP. The rule pays complete state and silent trace updates at every live successor;
there is no assumed semantic or callee-WP preservation callback.

The separate spec imports only definitions. Concrete registry links instantiate
the implemented resources in the shared 23-slot registry. Full target build
passed; independent physical-origin/cone audit and source review accompany
integration. This closes the restart rule, not a complete cycle/loop or boot
handler. Those continuations still need actual instruction proofs.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
