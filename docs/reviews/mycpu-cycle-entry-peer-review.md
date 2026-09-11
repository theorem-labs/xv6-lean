# Independent mycpu active-step entry review

Result: PASS for all five frozen MycpuCycleEntry modules and their STATUS.
No production correction is requested. The OpenAI Codex sail_audit agent
reviewed this independently of the coordinator's implementation.

Read Defs/Spec/Plan/Proofs/Link in full, generated Step.lean:321–396 and
Fetch.lean:232–284, and pinned SmodeCore.v:167–248. Also checked the concrete
Active and Fetch configurations, the actual common CycleBody footprint,
its body plans/native rules, and SupervisorFetchRead's structural/native
fold. The source progress lemmas retain a distinct post-fetch state for
TLB-filling translation; these rules explicitly specialize Bare fetch,
whose checked boundary preserves the owned register bundle. No general
TLB-preservation claim is inferred from that specialization.

The unconditional factor retains the interrupt, fetch-error, compressed,
base-instruction and ExecuteAs branches of the actual generated program.
The native proof derives no-interrupt dispatch under the stated Supervisor
and disabled-interrupt conditions. Structural widening preserves the
universal readAny branches from the underlying interrupt plan. Fetch uses
the actual boot-span context extraction and an existing discarded byte
window; it neither allocates instruction bytes nor upgrades a discarded
share or timestamp. Successful fetch follows from the owned actual word
through the native context read rule. The fixed-word continuation equality
holds for every tag. Error responses and alternative words, including
possible second fetches, remain in the original boundary tree.

Preparation writes nextPC using the instruction width, independently of
the read width. This matters for compressed instructions fetched through
the four-byte Ziccif branch. Pure transport proofs cover address/source
registers, Bare translation, TOR permissions, PMA/HTIF configuration, and
return conditions when moving from the original file to that prepared
file. The full 28-cell footprint is unique and includes the exact owned
cells required by each reused plan; it is not assembled by duplicating
resource bundles.

All four public contracts discharge the private entry helper's residual
body obligation. Scalar and return paths use actual RegisterPlan proofs;
loads and stores use actual generated memory boundaries and native TSO
rules. The result preserves exact instruction bits and the generated
single ExecuteAs redirection. `index_complete` covers all fourteen indices
with nine scalar instructions, two stores, two loads and return. No public
field assumes body correctness or an arbitrary machine-preservation fact.

One later guard accounts for fetch on scalar/return paths. The two memory
paths retain two guards and return separate fetch/data lower-bound receipts
without assuming an ordering between them. Loads preserve their arbitrary
DFrac word ownership and reservation. Stores require a full word, update it
to the original source-register value and return a cleared reservation.
All paths preserve the running context, persistent code span, whole owned
register bundle and specified custody for their ordinary terminal
continuation. No extra mask restriction or ghost allocation is introduced.

The STATUS accurately scopes this as a complete Bare active-step component.
It does not claim to establish Supervisor/Bare configuration, execute the
cycle's setup/retirement/clocks/restart, chain the complete function, supply
the source KPT/stack resources, prove its ABI result, or establish adequacy.

Validation: the owner reports the final 690-job build. This review freshly
ran `tools/lake.py env lean
/tmp/xv6-lean-research/MycpuCycleEntryAudit.lean`; the independent log is
`/tmp/xv6-lean-research/mycpu-cycle-entry-peer-audit.log`. All 52 logical
declarations from the five physical origins pass, including private and
generated roots. The traversal includes every transitive opaque body, type
and datatype constructor. Only propext/Classical.choice/Quot.sound occur,
with zero excluded roots and no unsafe/partial or Initial durable allocator
dependency. No implementation or dependency-build artifact was edited.

| File | Frozen SHA256 |
| --- | --- |
| Defs | `9e316d06f2013b325cf6926f4a559f7d86044044ed59155c32abcbab36e1b32e` |
| Spec | `1a2b79fe0f7a905dccdbefdc37614cfed216a24e43f406785ac7667dbf97a5d8` |
| Plan | `99bfe71f6f31064484b3b7335ee6da0cb12a1a3f1c2bb1716447577bb664d699` |
| Proofs | `b18909d9ca97ca65dfb48718284d821a266cf980957cfaade3f0b32a111ce6ec` |
| Link | `3bd2199bb8a03f1e79a26e7d2df18a4d15a32301310c8e86824d42c1aa4deb36` |

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
