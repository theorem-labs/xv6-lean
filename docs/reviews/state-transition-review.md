# Independent state/observation transition review

Result: no correction required. Reviewed frozen
`StateTransitionSpec/Proofs/Link` against the pinned source observation
interpretation (`RiscvPtsto.v:2192–2216`) and power transition composition
(`RiscvAdequacy.v:725–783,833–985`) at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`observed_step` requires an actual machine `Step`, an explicit proved
power-interpretation update and both observation halves. It first uses
native half agreement to identify the client's claimed history with the
actual existential past. After the explicit power update, it updates both
halves to that history followed by the actual event list. The exact future
prefix equation is preserved by append associativity, and actual
`step_observations_ok` supplies power alternation, boot count and UART wire
well-formedness. The caller cannot substitute an unrelated history or
invent an observation list.

`silent_step` also requires the actual `Step` and a proved resource update.
It preserves the observation ghost and uses the checked silent observation
lemma for the successor's well-formedness. It therefore needs no client
observation half for an empty event list. Both generic rules retain the
arbitrary returned resource `R`, and carry the actual fork-list length into
the successor interpretation.

The generic transition premise is deliberately a full Iris entailment
that a caller must prove. It is not an automatic hardware-preservation
assumption. The concrete power wrappers discharge it:

- `power_off_observed` constructs the actual PowerOff step, uses the proved
  fixed-power update and returns the old generation's death receipt. It
  requires both observation halves and removes exactly `[powerOff]` from
  the future trace.
- `power_on_observed` uses actual `BootShape`, the proved complete machine-era
  allocation, exact disk preservation and fresh registry insertion. It
  constructs the actual PowerOn step and uses `powerFork_length` for the
  eleven returned workers. The new era certificate and all declared boot
  clients are returned existentially; they are not replaced by an
  unspecified hardware update premise. Both observation halves are updated
  to the history followed by `[powerOn]`.

The wrappers do not establish client crash/trace invariants, distribute the
returned ownership to eleven worker WPs, or prove the power-loop WP. Their
comments correctly leave those obligations to later callers. The generic
rules and concrete wrappers preserve the same image-parametric machine and
fixed history/future interpretation.

Independent validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.StateTransitionLink
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/StateTransitionAudit.lean
```

The 416-job build passes. The independent audit checks 92 public/private
state-interpretation, allocation and transition declaration cones and
accepts only `propext`, `Classical.choice` and `Quot.sound`; output is
`/tmp/xv6-lean-research/state-transition-independent-axioms.log`. This review
made no production edits.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
