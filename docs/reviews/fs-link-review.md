# Independent filesystem link-camera review

Result: **PASS for the declared camera foundation.** Reviewed all five frozen
`MachCSL/Logic/FsLink{Defs,Spec,Proofs,Registry,Link}.lean` files and their status
record against `Xv6Cameras.v:559–580` and `FsStateLink.v:58–401` (sections 1–5b)
at pinned artifact `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The reviewer did
not implement this slice. No source file was edited or correction required.

## Carrier and ownership

The carrier matches the source construction: a file value or directory value
with a signed parent inode, a finite multiset of those values, its native
authoritative camera, and an outer finite map keyed by signed inode numbers.
Lean uses `ListPerm` for the finite multiset, `LeibnizMultiSet`, `Auth`, and
`ExtTreeMap Int` with the existing Heap camera instances. Inspection of the
native multiset camera confirmed ordinary multiplicity addition, empty core,
multiset inclusion, and the source-shaped cancellation/local-update law. No
separate count/parent product or assumed agreement law substitutes for this
camera.

Uniform replicas preserve the source zero, successor, singleton, addition,
size, and membership laws. `auth`, `toks`, and `tok` are native ownership of the
same singleton outer-map elements as their source counterparts. Runtime ghost
names remain explicit, and the capacity itself carries no resources.

The central validity proof obtains multiset inclusion from validity of the
actual authority/fragment composition. Both count and exact type/parent
agreement follow from that inclusion. In particular, a mismatched directory
parent is invalid and a zero-count authority excludes every singleton token.
The zero-count authority contains the empty multiset, so retyping is equality,
as in the source.

The empty-fragment corner case is preserved. It is a present outer-map key with
an empty fragment value, not the empty map. `toksElem_empty_not_unit` proves this
distinction and `empty_fragment_factor`/`toks_empty` prove the lawful factorization
from authority. The implementation does not identify empty-token ownership with
`emp`.

## Moves, routing, and allocation

`mint_update` and `return_update` use the native singleton-map and authority
update rules with the multiset local-update equation. Their arbitrary frames
are protected by those actual frame-preserving updates, rather than supplied
as preservation assumptions. The spatial one-token, batched, and explicitly
framed rules follow from them.

`return_reps` takes a pile at an arbitrary caller type. At zero count it imposes
no type equality; above zero the native validity law proves agreement before
deallocation. This matches `link_return_reps`'s source distinction. Splitting,
bounded prefix splitting, and list routing retain multiplicity and the source's
one-way affine routing direction.

`family_alloc` requires validity of the actual arbitrary family element.
`fullElem_valid` independently proves validity when an authority holds all its
own fragments, and `full_alloc` allocates that element and splits its ownership.
These do not assume a filesystem-wide link-validity result.

`FsLinkSpec` is implemented by the corresponding concrete native proofs and
`registryFsLinkSpec` discharges the capacity instance. Several source helper
exports have no separately named Lean wrapper: the singleton-token and
ownership definitional aliases, the full-element singleton-form rewrite, and
`link_auth_reps_le`. The last is the direct specialization of `auth_toks_le`
using `reps_size`; the others unfold or use the singleton-operation law already
used in the proofs. These are API naming differences, not missing camera laws
or added hypotheses.

## Registry and independent validation

The registry adds exactly slot 23. `registry_old` proves equality at every slot
below 23, and `registry_unused` preserves every slot at or above 24. The explicit
UART, invariant, heap, era, and machine capacities still select the existing
slots. The byte camera and shared monotone-counter equalities are preserved;
observation ownership remains at slot 11. The native invariant adapter reuses
the supplied runtime names and slots 16–19.

```text
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.FsLinkLink
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/FsLinkIndependentAudit.lean
```

The independent build passed 380 jobs. The fresh physical-module-origin audit
checked all 186 logical declarations in the five modules, including private
helpers, and their full logical dependency cones. Only `propext`,
`Classical.choice`, and `Quot.sound` occurred. No unsafe or partial semantic
dependency was found and zero runtime companions were excluded. Direct checks
of `registryFsLinkSpec`, `return_reps`, and `fullElem_valid` passed the same
allowlist.

The status correctly leaves source section 6 gathering, per-node/global link
elements, directory markers/type assignments, root keep-alive slack, and actual
image validity for later work. This foundation proves no snapshot allocation,
`snap_ok`, filesystem crash guarantee, or whole-system adequacy.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
