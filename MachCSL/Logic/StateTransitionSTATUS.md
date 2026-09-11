# State and observation transition composition

`observed_step` composes an actual machine step, a proved update of the
power/era resources and both observation halves. Agreement identifies the
actual past history. The update appends exactly the step's events, preserves
the fixed whole trace, removes those events from the future suffix and restores
the proved observation invariant at the successor. The client receives its
updated half and every resource returned by the power/era update.

`silent_step` needs no observation client because it preserves the current
history. It still requires both the actual silent machine step and a proved
power/era resource update. Neither generic rule supplies hardware ownership
preservation as an unproved fact.

`power_off_observed` and `power_on_observed` discharge those premises using
the concrete machine constructors and proved ghost transitions. Power-off
returns the death receipt; power-on returns the complete new era certificate
and declared machine clients, accounting for all eleven forked workers.
The durable disk is retained. Both rules require the observation client half;
the source's later trace-invariant custody hooks must provide it or an
equivalent update when building the full power WP.

`StateTransitionSpec` imports definitions only. The generic proof and concrete
link compile in a416-job build, and independent review/audit passes92
declaration cones with the standard three axioms. These are state/resource
transition laws, not a power-thread WP or a closed adequacy result.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
