# Dirty sets and persistent message history

Implemented against `iris/TsoGhost.v` at paper pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. Together with the existing ledger
and monotone-view modules, this implements the resources and all ghost-algebra
laws in that source file. It does not yet install the complete RISC-V state
interpretation, memory metadata resources or instruction/adequacy proofs.

| Source | Lean |
| --- | --- |
| `tsomem_logmG` (line 91) | `LogRA`, `LogRF`, `Capacity.logs` |
| `tsomem_dirtyG` (107) | `DirtyUR`, `DirtyRF`, `Capacity.dirty` |
| `dset_auth`, `dset_in` (144–147) | `dsetAuth`, `dsetIn` |
| persistent/timeless instances (149–154) | `dsetIn_persistent/timeless`, `dsetAuth_timeless` |
| `dset_alloc/halves/agree/lookup/get/insert` (156–203) | corresponding `dset_*` theorems |
| `dirty_ok`, persistence and monotonicity (384–398) | `dirtyOK`, `dirtyOK_persistent`, `dirtyOK_mono` |
| native Iris `ghost_map` laws used for source history | `log_alloc`, `log_agree`, `log_halves`, `log_lookup`, `log_elem_agree`, `log_insert`, `log_valid` |

`DirtyKey` is the unrestricted pair `Nat × PhysicalAddress`; no timestamp,
RAM-region, hart or alignment restriction is added. `DirtySet` is an
extensional finite tree set with Lean's lexicographic pair comparator.
`DirtyUR` uses native `LeibnizSet DirtySet`, the idempotent union camera,
under the authoritative camera. The full authority contains no baked-in
fragment. Membership owns a singleton fragment and is persistent.

`dset_get` remints membership under any fraction of the authority through a
basic update. `dset_insert` unions a singleton under full authority, including
when the key was already registered. `dset_insert_frame` explicitly retains
any Iris frame, so existing receipts do not prevent reminting or insertion.
`dsetAuth_fractional`, `dset_halves`, `dset_agree` and `dset_valid` expose
fractional splitting, agreement and validity.

`LogMap` is an extensional finite Nat-keyed tree map. Its values are the
existing machine `Message 64` type, including multi-byte partial-function
payloads and arbitrary Nat authors. Physical addresses range over `BitVec 64`,
so payload support is finite; this slice retains the existing machine
representation and makes no new cross-prover encoding-equivalence claim.
`logElem` is a discarded-fraction ghost-map receipt, hence persistent and
immutable while retained. `log_insert` requires the exact source fresh-key
condition and returns a persistent receipt immediately. The full authority
is not, by itself, an axiom that the machine log only appends: append-only
behavior must be maintained by the state interpretation and its update rules.

`LogRep entries log` means equality of every finite-map lookup with the actual
zero-indexed message-list lookup. `logRep_empty`, `logRep_fresh`,
`logRep_append` and `logRep_exists` prove initialization, exact append-index
freshness, extension and inhabitation for every log. `log_append_frame` adds
a message at `log.length`, retains any Iris frame and proves the new
representation condition. `log_lookup_list` reads the actual list through an
authority and persistent receipt.

`dirtyOK` preserves the exact source disjunction: the key's timestamp is
already below the bound, or there is a log entry whose successor index is
the timestamp and whose author is the bundle's agent. The second branch
imposes no condition on the key's address or that message's byte payload.
`dirtyOK_clean` and `dirtyOK_author` construct the two branches;
`dirtyOK_visible` derives the machine's actual `Memory.visible` predicate
when supplied the authoritative log, its explicit `LogRep` correspondence,
and a view at least the bound.

The separate registry extension is:

| Slot | Resource |
| --- | --- |
| 0 | unchanged byte-value map component |
| 1 | unchanged timestamp/pin map |
| 2 | unchanged authoritative per-agent views |
| 3 | unchanged shared mono-nat |
| 4 | log-message ghost map |
| 5 | authoritative monotone dirty set |

`registry_old` preserves every earlier slot; `registry_unused` preserves all
slots at least 6. Explicit witnesses construct `registryCapacity`,
`viewsCapacity` and `ledgerCapacity`. No old registry is changed and no second
mono-nat is introduced. Runtime names remain explicit assertion parameters.
The final whole-system registry must also include the source's outstanding
`gen_heap` metadata and all non-TSO capacities.

`TsoHistorySpec.lean` imports definitions only. `historySpec` supplies its
native Iris entailments, and `TsoHistoryLink.lean` explicitly instantiates
all three proved contracts (`registryHistorySpec`, `registryViewsSpec`,
`registryLedgerSpec`) in this six-slot registry. No callee proof is smuggled
into the independently importable specification.

Validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.TsoHistoryLink
```

The 221-job build passes; the history proof module takes about 1.1 seconds
and the link module about 0.7 seconds. The transitive namespace audit is
`/tmp/xv6-lean-research/TsoHistoryAudit.lean`, with output in
`/tmp/xv6-lean-research/tso-history-axioms.log`; it rejects every axiom except
`propext`, `Classical.choice` and `Quot.sound`. No `sorry`, custom axiom,
native decision procedure or bit-vector decision procedure is used.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
