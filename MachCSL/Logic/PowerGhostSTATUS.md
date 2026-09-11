# Fixed generation, start and observation resources

Implemented against pinned `iris/RiscvPtsto.v` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

| Source | Lean |
| --- | --- |
| `gen_auth/born/dead` (570–575) | `genAuth`, `genBorn`, `genDead` |
| `start_count/auth`, `gen_started` (601–606) | `startCount`, `startAuth`, `genStarted` |
| `obs_auth/frag`, `obs_pred_triv`, `obs_ledger` (683–705) | `obsAuth`, `obsFrag`, `obsPredTriv`, `obsLedger` |
| `obs_agree/update` (707–716) | `obs_agree`, `obs_update` |
| `obs_interp`, silent and close (2192–2218) | `obsInterp`, `obs_interp_silent`, `obs_interp_close` |

Generation and start counters use the existing shared native mono-nat resource
at slot 3, with different explicitly allocated runtime names. `genBorn n` is
a raw native lower bound at `n`; death and started certificates are raw lower
bounds at `n + 1`. Unlike the TSO log-length convenience receipt, there is no
pure zero branch. `gen_born_zero` therefore correctly requires a basic update.
Native allocation, monotone updates, receipt extraction, weakening and
validation are proved. Death and started validity give strict inequalities.
`gen_die` advances to the next generation and produces its predecessor's death
certificate; `start_mark` advances the start counter and produces a started
certificate.

`startCount g` is exactly the machine generation plus one when powered on.
`startCount_step` proves monotonicity for every actual `Machine.Step`, without
an assumed observation history. Power-off increments generation and leaves the
start count unchanged; power-on preserves generation and increments the start
count. The actual hart/device cases preserve both counters. `counterInterp`
is explicitly only these two counter conjuncts, and `counter_step` updates
this component through any machine step using native mono-nat updates.

The observation resource is a native `GhostVar` over complete lists of actual
`Machine.Observation` values. Both the state and client own exactly one half.
`obs_alloc` allocates both halves; agreement and joint update are checked.
An update requires the client half as well as the state half. The ledger
vocabulary is retained, with a timelessness instance when its client resource
is timeless; no invariant namespace or client invariant is assumed here.

`obsInterp` existentially stores a past history, its concatenation with the
future equaling the explicitly fixed whole trace, `Machine.ObservationsOK`
for that history and concrete state, and the machine's observation half.
This invariant includes exact power alternation, boot count and UART wire tie.
`obs_interp_silent` uses the actual silent machine step and preserves history.
`obs_interp_close` consumes an authority already updated to `history ++ events`
and proves the new interpretation from the actual step and trace decomposition.
It does not independently acquire the missing client half.
`obs_interp_finished` exposes the whole trace and its machine invariant when
the future is empty. `fixed_alloc` allocates only these fixed components for a
caller-supplied state/history satisfying the real observation invariant.

The registry extends `Reservations.registry` with observation ownership at
slot 11. All slots 0–10 and 12 onward are preserved. Explicit capacities for
the preceding resource families are derived. `sharedNat_same` proves that the
counter and view capacities use the identical slot-3 witness;
`genAuth_eq_shared_views` proves equality with the earlier native mono-nat
authority assertion at the same runtime name. There is no second mono-nat
camera and no new resource at slot 12 or beyond.

`PowerGhostSpec.lean` imports definitions only. `powerGhostSpec` proves that
contract, and `PowerGhostLink.lean` instantiates it in the extended registry.
The link also instantiates the already proved global register contract at
its preserved register capacity.

Validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.PowerGhostLink
```

The build passes 374 jobs; the proof and link modules take approximately one
second each. `/tmp/xv6-lean-research/PowerGhostAudit.lean` audits every new
public/private declaration transitively, rejecting all axioms except `propext`,
`Classical.choice` and `Quot.sound`; log:
`/tmp/xv6-lean-research/power-ghost-axioms.log`. No `sorry`, custom axiom, native
evaluator or bit-vector decision procedure is used.

Outstanding: the complete era record and registry, era certificates, namespace
invariants and masks, fixed durable-disk composition, client observation hooks,
full power/state interpretation, instruction WP lifting and adequacy. This
slice does not invent a truncated era type or claim the full machine is
interpreted. The translation one-shot, swap counter and other neighboring
source resources are separate outstanding interfaces.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
