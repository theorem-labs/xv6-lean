# Inode link and top custody boundary

Approved implementation boundary: `IcacheInodeCustody{Defs,Spec,PureProofs,Proofs,Link}`
and its STATUS, corresponding to pinned `InodeRegion.v:2113–2545` and the
bare/free-node vocabulary at 463–492. Existing frozen components are reused.

The pure multiplicity is `n + (if ty = 1 ∧ n ≠ 0 then 1 else 0)`.
A directory's zero-to-one link-count transition changes multiplicity by two;
other increments change it by one. The API retains unsigned record-field
hypotheses as equalities of integers, so overflowing 16-bit changes do not
silently satisfy a nonmodular increment premise. A directory register value
carries an arbitrary parent, whose value is not constrained by `regOK`.
The separate directory payload, outside this boundary, supplies that tie.

At the same supplied filesystem view and native FsLink capacity, `ireg_lnk_at`
contains an existential register value, its exact type predicate, the native
uniform-multiset authority at this inode and multiplicity, and one extra
singleton fragment exactly when the inode number is one. The root fragment
is retained by updates and counted in the root lower-bound theorem. Empty
count retyping at the root is refuted by native authority/fragment validity;
no pure axiom that the root is allocated is introduced. Other directory-entry
fragments remain outside this predicate.

The native rules cover stable records, zero-count retyping, multiplicity
increment/mint, zero-count fill with a chosen value, decrement/return, pile
bounds, token type/agreement and liveness, and root accounting. No name is
allocated. Generic capacities and names stay explicit, and the concrete
Link uses existing FsLink slot 23 and FsTop slot 25 in the current LogTx
registry. There is no new registry slot or assumed world allocation.

`freeNode d` retains the exact input record, 256 zero indirect entries and
an empty data map. Existing `InodeRegionImage.bare` is size zero plus exactly
13 zero addresses; it does not impose a type or link-count restriction.
The source `DurableNode.Node.Bare` additionally imposes zero links. Its
conversion to/from the free-node helper retains that distinction.
`ireg_top_park` owns a full top fragment for an arbitrary native durable node
and the pure implication that a zero-type record is bare and the node equals
`freeNode d`. Nonzero records impose no further tie. Introduction and opening
preserve precisely this guarded condition and the existing full fragment.

The boundary does not allocate boot state or prove an entire inode slot,
epoch receipt, escrow protocol, claim-box transaction pin, or collection.
Those remain source dependencies to assemble from the independently checked
resources. Defs contain all predicates and helper data; proof files contain
only checked laws. Validation uses the Lean kernel and a complete
physical-origin dependency audit including opaque theorem bodies and
inductive constructor types, with only the standard three axioms allowed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
