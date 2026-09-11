# Native inode link and top custody

The five `IcacheInodeCustody{Defs,Spec,PureProofs,Proofs,Link}` modules are
frozen after owner validation. They implement pinned `InodeRegion.v:2113–2545`
with the free-node helper at 463–492. The approved design is
`docs/design/inode-custody-boundary.md`.

| Source | Lean mapping |
| --- | --- |
| 463–492 | Existing `InodeRegionImage.bare`, exact `freeNode`, record projection, bare-node equality, free-node bare law with explicit zero links |
| 2113–2201 | `ireg_nl`, `ireg_mult_at`, `ireg_mult`, bounds, zero, exact integer-field bump/drop and `ireg_dot_delta` |
| 2208–2222 | `ireg_reg_ok`, with directory parent unrestricted, and existence |
| 2237–2312 | Native `ireg_keep`, `ireg_lnk_at`, `ireg_lnk`, Timeless, field stability and zero-count retyping |
| 2320–2385 | Native count increase, chosen-value fill and count decrease, with exact minted/returned repeated fragment piles |
| 2396–2477 | Pile size bounds, live/type/agreement readings, root alive and held-pile bound |
| 2500–2541 | Guarded `ireg_top_park`, Timeless, nonzero/free introduction and zero-type opening |

The link predicate owns only the per-inode uniform-multiset authority plus
the root's extra singleton. Directory-entry fragments remain in their
separate payload. The root keep-alive fragment is retained by every update;
the zero-count retype and fill cases at the root derive a contradiction
from actual native authority/fragment validity. The root held-pile bound
combines the separate singleton with the caller's whole pile before invoking
native validity. It does not count one fragment twice or assume a pure
root-allocation clause.

Multiplicity is zero when the link count is zero, including directories.
The directory boundary from zero to one changes multiplicity by two, while
other link increments change it by one. The public increment/decrement laws
retain the exact source unsigned-field equalities as integer equations, so
modular overflow does not become an ordinary increment. The register-type
predicate does not tie a directory's stored parent to another value.

The top predicate holds a full native fragment for the complete arbitrary
`DurableNode.Node`. Its tie to the record is conditional on type zero. At a
nonzero record, the parked node is unrestricted. At type zero, the record is
bare and the node is exactly the input record, 256 zero entries and an empty
block map. The bare-record predicate imposes neither type nor link count;
`freeNode_bare` explicitly needs zero links to prove the stronger source
node-bare predicate. The existing `InodeRegionImageProofs.ireg_bare_of_fn_bare`
already supplies the converse record projection and is not duplicated.

All native rules take the same supplied `FsView.View`, link and top
capacities and names. `nativeSpec` uses the existing LogTx registry's
FsLink slot 23 and FsTop slot 25. There is no new slot, ghost allocation,
initial-snapshot constructor, complete slot invariant, epoch or escrow
assumption. These laws expose the source custody resources for later
inode-region composition; they do not claim whole-region boot allocation.

Validation: `python3 tools/lake.py build MachCSL.Logic.IcacheInodeCustodyLink`
passes all 475 jobs. There are 30 named theorems and four Timeless instances.
The fresh `/tmp/xv6-lean-research/IcacheInodeCustodyOwnerAudit.lean` checks
all 73 logical declarations from the five physical module origins, including
private helpers, all opaque theorem bodies, declaration types and inductive
constructor types. All pass with only `propext`, `Classical.choice`, and
`Quot.sound`; zero roots are excluded and no unsafe/partial or
`FsDurSnapshot.Initial` dependency occurs.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
