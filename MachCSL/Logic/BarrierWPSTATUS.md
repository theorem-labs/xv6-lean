# Native barrier leaf rules

Source: pinned `iris/HartBarrier.v:58–306`, especially `pub_step`,
`ghost_step`, and their two native WP leaves, at xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`BarrierWPDefs` defines the actual event projection and resume, the exact
`fencePost` successor, and the two source client obligations. `ghostStep`
grants a basic update over the actual full native heap interpretation and
TSO interpretation at a fixed state, restoring both with the client's `Q`.
`pubStep` additionally grants the own-publication bound for this CPU and
the native view lower bound receipt at its resulting view. It never grants
a global-log-top bound.

`BarrierWPProofs` proves the real live machine step and uniqueness, with no
events or forks. The successor changes only this CPU's view: registers,
memory, devices, generation, power, reservations, initial image, log, and
other CPU views remain equal. A non-draining fence leaves the entire state
equal. Every barrier kind follows the existing source `fenceDrains`
classifier, including its non-draining `rw,w` case.

The full-power ghost updates first extract the actual memory/view bounds,
apply the already-proved `TsoRead.power_advance`, and open the registered era
at that exact successor. The callback receives only the heap and TSO
conjuncts; the remaining five era conjuncts and all fixed-state ownership are
framed and restored. `power_publish` requires the real draining classifier
and supplies only `ownPub ≤ current view` plus that view's receipt.
`power_ghost` exposes neither gift. Its internal advancement helper can mint
a persistent receipt, which is discarded without reaching the client.

`wp_ghost` and `wp_publish` use native `NotStuck` WP with a guarded
continuation and the actual fixed observation interpretation. The generation
certificate proves either a current live thread or an older dead generation.
The latter follows the actual dead-thread step and already-proved guarded
dead-thread WP; it does not treat a live failure as a dead step. Silent trace
preservation is discharged by the actual barrier step. Both public rules
instantiate a private common lifting lemma with the complete proved
resource updates; clients have no full-state-preservation premise.

| Source symbol | Lean symbol |
| --- | --- |
| `hbar_at`, `hbar_resume`, `hbar_at_inv` | `barrierAt`, `barrierResume`, `barrierAt_inv` |
| `pub_step`, `pub_step_id` | `pubStep`, `pubStep_id` |
| `ghost_step`, `ghost_step_id` | `ghostStep`, `ghostStep_id` |
| `pub_step_of_ghost_step` | `pubStep_of_ghostStep` |
| `wp_hart_barrier` | `wp_publish`, `wp_publish_at` |
| `wp_hart_barrier_gs` | `wp_ghost`, `wp_ghost_at` |

The constructor rules preserve the actual Unit continuation; the `*_at`
wrappers use the checked projection/resume inversion. `wp_identity` supplies
the trivial ghost obligation for any barrier. The more general source
`mctx`/`swp` abstraction and its separate composition rules are not claimed
by these direct-node wrappers. No particular client publication protocol,
spinlock invariant, or instruction decoder proof is supplied here.

`BarrierWPSpec` separates the client contract from the implementation.
`BarrierWPLink` instantiates it at the existing shared 23-slot
`UartGhost.machineCapacity` and reuses the caller's actual allocated native
invariant names. No camera or invariant world is allocated. The generic
proofs also apply to later capacity extensions without changing slots.

Validation: `python3 tools/lake.py build MachCSL.Logic.BarrierWPLink` passed
431 jobs; the proof module compiled in 1.2 s and the link in 827 ms.
`python3 tools/lake.py env lean /tmp/xv6-lean-research/BarrierWPAudit.lean`
checked all 52 declarations physically originating in the four modules,
including private and generated helpers. All use only `propext`,
`Classical.choice`, and `Quot.sound`. Recursive traversal of all statement
and proof bodies found no unsafe or partial semantic dependencies. No
runtime companions were excluded. Independent root review passed; see docs/reviews/barrier-wp-review.md.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
