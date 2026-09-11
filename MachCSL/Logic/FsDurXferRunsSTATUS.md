# Native transport runs and mixed fractions

Frozen bounded port of `iris/FsDurXfer.v` §§0–2d, lines 83–565, at
`arxiv-v1` (`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`), with its
`snap_gamma_agree` law from lines1123–1130. The full 1357-line source was
read before selecting this prerequisite boundary. Five modules contain
43 named laws and the exact source run predicates.

`Run` is the source pair carrier `(Int × Int) × List Byte`. Its block
and offset are signed, byte lists have no hidden size condition, and its
map uses the existing signed `byteRun`. `runUnion` is a total, ordered,
left-biased fold. `RunsDisjoint` quantifies distinct list positions, not
unequal run values: repeated empty runs remain legal. The pure laws
include cons/append decomposition, head-versus-union disjointness, and
lookup provenance. Checked generic regressions establish repeated-empty
run legality and first-payload precedence for overlapping runs.

`QRun`, `atShare`, `strip`, and `SharesOK` preserve the exact mixed-share
carrier and the requirement that each run's fraction has an invalid
double. All three native fraction forms are retained: source Own is
`DFrac.own`, Discarded is `DFrac.discard`, and Both is `DFrac.ownDiscard`.
The arithmetic distinguishes the strict bound for Own from the nonstrict
bound for Both. It proves that individually invalid doubles imply an
invalid mixed pair, and that a share strictly above one half has an
invalid owned double. It does not replace this condition with a fixed
three-quarter share or silently restrict fractions to Own.

The native `phiMap`, `phiRuns`, `phiMapQ`, and `phiRunsQ` laws establish:

- each run's byte-range predicate equals its finite-map byte predicate;
- incompatible fractions and `PhiExcl` derive disjoint byte maps;
- native run ownership derives positional disjointness, including mixed
  runs under `SharesOK`, by selecting one position and deleting its
  resource before selecting the other;
- under proved disjointness, full run ownership is equivalent in both
  directions to ownership of the ordered union;
- `PhiAgree view A M` quantifies every fraction and makes `A` plus one
  native byte fragment read the same byte in `M`;
- map/run ownership yields inclusion in that source map. Mixed-run
  inclusion needs no disjointness premise, exactly as in the source;
- the existing native snapshot authority satisfies `PhiAgree`, by one
  `ghost_map_lookup` at the existing disk camera.

Every disjointness and inclusion result is pure, enabling later callers
to retain the original resources. No allocator, fresh name, camera,
filesystem validity assumption, or abstract state reconstruction is used.
No malformed block-width restriction is added to these arbitrary run
lists; the ordered union law also applies when their byte ranges overlap.

Validation: `python3 tools/lake.py build
MachCSL.Logic.FsDurXferRunsProofs` passes 402 jobs. A fresh physical-origin
audit checks all 89 declarations and their transitive types,
theorem/opaque bodies (`allowOpaque := true`), and referenced constructor
fields. Only `propext`, `Classical.choice`, and `Quot.sound` occur;
no unsafe or partial semantic dependency, zero exclusions. The audit
additionally rejects every `FsDurSnapshot.Initial` dependency; none
occurs. Working audit source:
`/tmp/xv6-lean-research/FsDurXferRunsOwnerAudit.lean`.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.

Coordinator source comparison and independent audit approved this boundary;
see [the review](../../docs/reviews/fs-dur-xfer-runs-review.md).

Next obligations are the structural inode/free-pool/whole-footprint run
correspondence (§3), then install, source-instance transport, and runtime
epoch cloning (§4 and FsDurSnap). These run laws do not themselves claim
any runtime transport or full kernel crash refinement.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
