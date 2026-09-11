# Link-family construction and image choices

Source: `xv6iris` tag `arxiv-v1`, commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`LinkFamilyDefs.lean` uses the actual native `MachCSL.Logic.FsLink.FamilyRA`:
a finite inode map of authoritative finite multisets of `IType`. It adds
no camera, axiom, resource slot, validity assumption, or reduced node carrier.
The image and inode maps retain all rounded-region entries, including free
inodes. Both modules are generic and import no concrete image literals.

| Pinned source | Lean contract |
| --- | --- |
| `FsStateInode.v:934–970` `fn_ity_ok`, `fn_mult` | `KindOK`, `multiplicity`, existence, zero, lower-bound and live-directory laws |
| `FsStateInode.v:985–1036` `ent_tokenless`, `ent_ty_ok`, `fn_dd`, `ent_dset_ok` | `tokenless`, `EntryTypeOK`, `parentEntry`, `MarkersOK` |
| `FsStateInode.v:1061–1086` `node_exact`, `ent_elem`, `link_elem_node`, `node_ent_ok` | `ExactCount`, `entryElem`, `nodeElem`, `NodeEntOK` |
| `FsState.v:400–416` choice projections and whole-map elements | `Choice`, `choiceMarkers`, `choiceValue`, `choiceTypes`, `ElemOK`, `elem` |
| `FsDurImg.v:717–744` `img_v`, `img_f` | Total `imageValue`, `imageChoice`, including absent-entry file default |
| `FsDurImg.v:908–1007` `img_link_elem_ok` | `image_node_ent_ok`, `image_elem_ok`, `bootImage_elem_ok` |

The token exemption preserves the executable formula exactly. Orphan dot
and dotdot entries are exempt, and **every nondot self-target is exempt**,
even when its name is neither dot name. Live dot entries retain their token.
The dot-parent condition retains its guard: a missing parent entry imposes
no constraint on the directory-parent value. No additional root-only or
well-formed-tree restriction has been imposed on these definitions.

`entriesElem` and `elem` use Iris's native finite-map `bigOpM`, whose list
enumeration and commutative-monoid laws justify the finite representation.
The checked insert/extract laws bridge Iris's `alter`-based insert/delete to
the concrete `ExtTreeMap.insert`/`erase`. Only new-key insert factors the
element; overriding an existing authority is not treated as a fresh factor.
Choice congruence needs equality of token types only at nonexempt entries.
Marker choices are pure predicates and do not enter the camera element.

`image_elem_ok` uses exactly the source theorem's two boolean premises,
`fsimgValid image sb = true` and `regionValid image sb nib = true`. Its proof
establishes that every directory in the full rounded region is the root,
the root has multiplicity two and satisfies the empty marker count, and
every nonexempt entry has the required target type. Target bounds and live
status come from the checked directory's actual first-winner byte lookup.
The `BootImageWF` projection uses its existing image and region fields.

Validation: `python3 tools/lake.py build Xv6.Fs.LinkFamilyProofs` passed
240 jobs; the new proof module took 1.5 seconds. Its enforced transitive
axiom audit checked all 105 public/private namespace declarations, including
definitions, accepting only `propext`, `Classical.choice`, and `Quot.sound`.
Kernel-checked edge facts cover ordinary self-exemption, live/orphan dots,
and present versus absent dot-parent checks. No `native_decide`, `bv_decide`,
`sorry`, custom axiom, unsafe definition, or evaluator assertion is used.

The subsequent LinkSupply/LinkDirectory/LinkImage layers now prove native
camera validity of the complete image family together with the root's spare
token (`FsDurImg.img_link_valid`), including counting and root slack. `ElemOK` is the source's
pointwise pure clause and does not imply that camera-validity theorem.
Native ownership packing/scattering, the later snapshot predicates and
resource allocation remain subsequent source dependencies, not assumed
premises here. The frozen `FsLink` modules were not modified.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
