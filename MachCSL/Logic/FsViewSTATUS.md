# Fractional filesystem views and native disk instance

Frozen source slice: the view, range, block, fractional-splitting, and
exclusivity theory of `FsStateDefs.v:98–485`, plus
`FsDurBytes.v:363–388`'s durable view instance, at xv6iris `arxiv-v1`
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`FsViewDefs` keeps the source view record: a predicate indexed by `DFrac`,
signed byte address and byte value, and two independent runtime ghost names
for the link and top-level inode maps. Ranges use exact signed addresses
`block * 1024 + offset + index`; whole-block ownership additionally requires
exactly 1024 bytes. Full-share forms are definitionally the `.own 1` forms.

`FsViewSpec` states precisely the source hypotheses:

- `PhiExcl` bounds the sum of **arbitrary discardable fractions** held at
  one byte address; it does not assume the byte values agree.
- `PhiFrac` is the two-way splitting law for ordinary positive owned
  fractions `.own (q1 + q2)` only.
- `GTimeless` quantifies over every fraction, address, and byte.
- `ViewShed` asks only for a one-way split of a full-share byte into two
  views; it is not a rejoining or agreement assumption.

The generic proofs retain the nonempty-run premises for byte-range
exclusion, the full-length block premise, and invalid-fraction-sum premises.
They include append, fraction split/rejoin, full-to-three-quarter/quarter
split, constant-share views and one-way shedding, share validity, exclusion,
and non-aliasing. Full ownership excludes every other `DFrac` by the actual
camera's `valid_own_op` law; two three-quarter shares are invalid by kernel
checked rational arithmetic. No informal discard exception is used.

`gammaQ` deliberately ignores its incoming fraction and preserves the link
and top names. It inherits timelessness but **has no inferred `PhiExcl`
instance**. Generic split/validity lemmas take the required source law as an
explicit hypothesis; these hypotheses are not new global camera axioms.

`FsViewLink.snapGamma` supplies the actual native `ghost_map_elem` predicate
from the existing `Disk.Capacity.image`. Native proofs establish its
fraction-sum validity and timelessness. An additional proved `PhiFrac` law
uses the camera's existing fractional instance; durable source consumers
require only the former two laws. The `.own 1` byte is definitionally the
existing `Disk.imageByte`. The concrete `registryGamma` uses
`FsLink.eraCapacity.disk` and proves its camera index is **slot 12**; it
allocates no new camera or name and mutates no registry. Link and top names
remain explicit arguments, with allocation deferred to their actual caller.

Validation: `python3 tools/lake.py build MachCSL.Logic.FsViewLink` passes
381 jobs, with the generic proofs and native link each taking about one
second. A fresh physical-origin audit covers all **86 declarations** in the
four modules and their transitive types, bodies, and referenced constructor
fields. Only `propext`, `Classical.choice`, and `Quot.sound` occur; no unsafe
or partial semantic dependency, and zero excluded declarations. Audit source
is retained at `/tmp/xv6-lean-research/FsViewOwnerAudit.lean` in the working
environment. No `sorry`, custom axiom, `native_decide`, or `bv_decide` is
used. Independent review passed; see `docs/reviews/fs-view-review.md`.
The root also reran the full 86-declaration dependency audit successfully.

The source `big_sepM_map_seqZ_gen` bridge is a remaining dependency of the
byte-map flattening layer; this checkpoint implements the list-based view
theory and its native byte instance. Remaining native snapshot dependencies
are the top inode camera, nested inode/bitmap/filesystem ownership and link
gather/scatter, exact block-to-byte flattening, footprint carving, and
`fs_snap`/`P_dur` allocation and transport. **Native `P_dur` remains
unimplemented**: the already proved pure `Snapshot.OK` is not substituted
for that resource. Slot 24 is reserved for locks and slot 25 is reserved
for the future top inode camera; neither is changed here.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
