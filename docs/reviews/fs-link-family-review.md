# Independent filesystem link-family review

Result: **PASS for the declared construction and pointwise image theorem.**
Reviewed frozen `Xv6/Fs/LinkFamily{Defs,Proofs}.lean` and its status against
`FsStateInode.v:934–1086`, `FsState.v:400–416`, and
`FsDurImg.v:717–765,908–1030` at pinned artifact
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The reviewer did not implement
these files. No source edit or correction was required.

## Exact node and family construction

The definitions use the existing arbitrary durable-node carrier and native
`FsLink.FamilyRA`. `KindOK` distinguishes directories from every other node
kind without adding local-validity assumptions. Multiplicity is exactly `nlink`
plus one for a non-orphan directory; every zero-link node therefore has zero
multiplicity. No new camera or registry slot is introduced.

`tokenless` matches the executable source formula. Either dot name is exempt
at an orphan, and every non-dot self-target is exempt, including an ordinary
name. A live dot is not exempt. This correctly follows the source definition
despite its nearby prose describing the self-target case more narrowly.

`EntryTypeOK` retains all source branches. A dot constrains a directory-parent
value only when a parent entry exists; dotdot has no type condition. An ordinary
name has exactly directory/self or file type according to its marker bit.
`MarkersOK` requires presence and excludes both dot names; `ExactCount` has the
source directory guard and orphan-dependent offset. `NodeEntOK` combines all
three node conditions with the entry-type condition only for present,
nonexempt entries. No tree well-formedness, root-only condition, or cross-node
validity is built into these generic predicates.

`entriesElem` and `elem` are actual native finite-map `bigOpM` constructions.
The per-node contribution is its authority composed with all nonexempt entry
tokens; exempt entries contribute the camera unit. The global construction
includes every stored inode. The insertion factorization requires the key to
be absent, so it does not treat replacement of an existing authority as adding
a fresh independent authority. Extraction uses the actual erase map. The
bridges to Iris's insert/delete operations are proved extensionally.

The choice is a total function on signed inode keys, with arbitrary marker
sets, authority values, and per-name token values. Congruence requires value
agreement only on stored inodes and token-type agreement only on their
nonexempt entries. Marker choices do not enter the camera element itself;
their conditions remain in `ElemOK`.

## Image specialization

`imageValue` and `imageChoice` reproduce the source total functions, including
keys outside the inode map. They select directory parent 1 for directories,
file otherwise, empty markers, and the target node's value for a present
directory entry, with file as the absent-entry default.

`image_elem_ok` uses precisely `fsimgValid image sb = true` and
`regionValid image sb nib = true`. No link-count equality, root-no-self
predicate, rounded-region coverage bound, concrete image literal, or native
camera-validity premise is added. The proof first uses the region-free clause
to show that any directory in the full rounded region is inside the advertised
inode bound, then uses image validity to identify it with root inode 1. Free
and padded inodes remain in the map.

For the root, the checked image properties establish directory kind, `nlink=1`,
non-orphan status, and therefore multiplicity **2**. Empty markers satisfy its
exact-count condition. Dot points to root and its existing dotdot entry fixes
the same parent value. An ordinary nonexempt name cannot target itself; its
actual first-winner directory-byte lookup establishes target bounds, and image
validity rules out another directory. This yields the required file type.
The argument follows the branches of source `img_link_elem_ok` directly.

The `bootImage_elem_ok` convenience theorem merely projects the two existing
Boolean facts from `BootImageWF`. It does not strengthen the generic theorem's
premises.

## Independent validation and remaining obligation

```text
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Fs.LinkFamilyProofs
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/LinkFamilyIndependentAudit.lean
```

The independent build passed 240 jobs. Its embedded namespace audit checked
105 declarations. The fresh physical-module-origin audit checked **107**
logical declarations from both modules, including the two generated equation
lemmas `Xv6.Fs.dotName.eq_1` and `Xv6.Fs.dotdotName.eq_1` outside the filtered
namespace, every private helper, and
their complete statement/proof dependency cones. Only `propext`,
`Classical.choice`, and `Quot.sound` occurred; no unsafe or partial semantic
dependency was found and zero runtime companions were excluded. Direct axiom
checks of `image_elem_ok` and `image_root_multiplicity` passed. A recursive local
import inspection found no generated or concrete image modules.

Crucially, `ElemOK` is the source pointwise type/count condition, **not** native
camera validity of the combined element. Source `img_link_valid` additionally
needs the link accounting, root-no-self condition, region coverage, and root
spare-token argument. Those, ownership gathering/scattering, and later snapshot
allocation remain separate obligations. The status distinguishes them correctly;
this review makes no filesystem allocation or crash-correctness claim.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
