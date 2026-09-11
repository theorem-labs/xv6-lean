# Running contexts and physical byte reads



This slice implements the running-context and physical-byte ownership
needed by the supervisor `mycpu` stack proof. It is not a translated-memory,
stack, instruction, or function WP. The source is `iris/TsoCtx.v` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

| Source | Lean |
|---|---|
| `CtxId`, lines 91–113 | `TsoContext.CtxId` with explicit `bound` and `dirty` names |
| `ctx_at`, lines 244–247 | `ctxAt` |
| `ctx_at_halves`, lines 249–258 | `ctxAt_halves` |
| `ctx_at_agree`, lines 260–267 | `ctxAt_agree` |
| `own_context_def`, lines 294–305 | `ownContext` |
| `ctx_floor`, its zero/weakening laws, lines 325–337 | `floor`, `floor_zero`, `floor_le` |
| `own_context_floor_view`, lines 349–365 | `ownContext_floor_view` |
| `own_context_excl`, lines 476–483 | `ownContext_exclusive`, including different harts |
| `own_context_boot`, lines 534–547 | `allocate` |
| `ctx_phys_pointsto_def`, lines 2095–2101 | `physPointsto` |
| physical core of `ctx_load_ok`, lines 1804–1875 | `load_fact`, preserving gate `load` |
| actual era specialization | `era_load` |
| explicit proof contract and implementation | `TsoContextSpec`, `actual`, `registrySpec` |

The physical assertion owns the actual byte at its fraction, matching
`(timestamp, payNone)` ownership, and the source clean-or-dirty resource.
The clean alternative includes the zero-timestamp case of `llb`. The dirty
set is the full finite set of `(Nat, BitVec 64)` keys, not a bounded sample.
The running token owns both full context authorities, its view receipt,
dirty watermark and every dirty key's clean-or-authored justification.

`load` accepts the complete native heap, including metadata, and actual
TSO interpretation with an explicit era image. It returns those exact
resources together with the running token and the byte assertion, and
proves the byte is read at **every** view at least the actual hart view.
The dirty case uses the current log's actual author receipt, allowing
forwarding without assuming the write timestamp is below the read view.
No machine state, view, timestamp or ghost authority is updated by this
load gate. Arbitrary DFrac ownership and arbitrary timestamps are retained.

The implementation reuses the canonical registry through `LockSet.registry`.
The context bound uses existing mono-nat slot 3 and the dirty set uses slot
5; log, byte and timestamp capacities remain slots 4, 0 and 1. No functor
or camera is added. `ofEraCapacity` and `ofEraNames` make the coupling to the
existing era explicit; `era_load` preserves all other era conjuncts.
Allocation mints real fresh authority resources for an empty context. It
does not claim that current boot already allocated a context for each CPU.

The store gate, context migration/parking, VA mapping claims, stack algebra,
SIE resources and supervisor-cycle proof remain unimplemented in this slice.
The next store implementation must register new dirty keys using the actual
ordinary-store message and preserve every old key; it must not advance the
hart view merely to make stack readback easier. See
[`mycpu-wp-boundary.md`](../../../docs/design/mycpu-wp-boundary.md).

Validation: `python3 tools/lake.py build MachCSL.Logic.TsoContextLink`
completed 421 jobs. The fresh physical-module audit checked all **70 logical
declarations across four modules**, including opaque theorem bodies and
inductive constructors, with zero exclusions. Only `propext`,
`Classical.choice`, and `Quot.sound` occur; no unsafe or partial declaration
occurs in their logical dependency cones. The implementation contract,
load-preservation theorem and era specialization were also checked with
`#print axioms`. Raw evidence is outside the repository at
`/tmp/xv6-lean-research/TsoContextAudit.lean` and `tso-context-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
