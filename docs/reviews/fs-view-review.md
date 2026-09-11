# Filesystem view independent review

Reviewed frozen `FsView{Defs,Spec,Proofs,Link}.lean` and status against
`FsStateDefs.v:90–485` and `FsDurBytes.v:363–388` at pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, with the native disk camera,
`DFrac`, `Fractional`, and `BigSepL` APIs used by the implementation.
Result: pass; no correction required for this declared view-theory slice.

`View` preserves all three source fields: a discardable-fraction-indexed
byte predicate at signed addresses, and separate link/top ghost names.
`byteRangeQ` uses exactly `block*1024 + offset + index` with no nonnegative
address or offset restriction. Whole-block ownership includes the exact
1024-byte length. Full-share forms and constant-share forms reduce to the
source predicates without altering the ghost-name fields.

The four abstract laws retain their source quantifiers. `PhiExcl` bounds
the combined arbitrary `DFrac` shares without requiring the values to be
equal; `PhiFrac` is a two-way ordinary-positive-share law; timelessness
covers every fraction/address/value; `ViewShed` requires only a one-way
full-share split. None is inserted as a global axiom. The generic proofs
retain the nonempty premises for range exclusion and the invalid combined
share premises for arbitrary fractional exclusion. Exact block length
supplies nonemptiness for block laws. Full shares exclude even discarded
shares by the native camera law, and the three-quarter calculation is
checked rational arithmetic.

`gammaQ` deliberately ignores its incoming fraction and copies both names.
It inherits timelessness, but the implementation correctly supplies no
exclusivity or fractional instance for this constant-share view. Shedding
uses the original view's fractional hypothesis and the specified shares;
it does not infer a general rejoining or value-agreement property for
arbitrary view predicates.

`snapGamma` uses actual native `ghost_map_elem` from `Disk.Capacity.image`.
Its full byte is definitionally the existing `Disk.imageByte`, its validity
and timelessness come from that same camera, and its extra fractional law
is proved rather than assumed. The source durable consumers require only
exclusivity/timelessness; exposing this additional valid camera law does
not alter their contracts. The concrete link's slot certificate checks
exactly existing disk slot 12. Runtime byte/link/top names remain caller
parameters, with no additional camera, registry mutation, or duplicate
byte authority allocation.

The status accurately leaves `big_sepM_map_seqZ_gen`, the top inode camera,
nested filesystem ownership, byte-map flattening/carving, and full native
`fs_snap`/`P_dur` allocation and transport outside this checkpoint. Pure
`Snapshot.OK` is not substituted for native durable resource ownership.

Independent validation:

- `python3 tools/lake.py build MachCSL.Logic.MemoryWriteWPLink MachCSL.Logic.FsViewLink`:
  passed 458 jobs, including the complete FsView target.
- `/tmp/xv6-lean-research/FsViewIndependentAudit.lean`: independently checked
  all 86 physical logical declarations in the four modules, including
  private/generated helpers, and their full recursive type/body dependency
  cones. Only `propext`, `Classical.choice`, and `Quot.sound`; no unsafe or
  partial dependency and zero excluded runtime companions.

The reviewing agent did not implement these four files. Prior contribution
to the reused disk ownership/capacity implementation is disclosed; this is
an independent review of the new view layer, not an independent
reimplementation of all its dependencies.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
