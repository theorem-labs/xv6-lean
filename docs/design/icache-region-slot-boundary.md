# Complete native inode slot and pointwise boot boundary

Approved boundary: `IcacheRegionSlot{Defs,Spec,Proofs,BootProofs,Link}` and
STATUS. This assembles the exact source `InodeRegion.v:2634–2730` slot from
its already implemented native components, plus the pointwise boot routing
in `IcacheBoot.v:773–842`. It creates no camera or invariant assumption.

The slot keeps the source association: an existential r/c/f/n body, then
the epoch receipt, then filesystem link custody. The body contains native
reference authority with its pure count relation; the complete link-ok
predicate; the disjunction of absent claim and native open regime; the
region count half; exact raw claim/freeze validity; the paired native
shelter; freeze mirror; and the complete arm. Raw absent/invalid claim and
freeze carriers stay unchanged. No existential is replaced by a supplied
oracle or a Boolean tag.

The arm is exactly a disjunction. Its nonpending branch owns either the IN
pure condition, full record and guarded top park, or the MARKED pure
condition and marker; both alternatives also own an existential full
registry row. Its pending branch owns the zero-type condition, full record,
an existential structural registry half, actual `region_pending` (which
owns the second half and native committed fragment), and the guarded top
park. The two half-name pairs are not identified definitionally; native
agreement remains the source reason they agree. No escrow invariant is
smuggled into this Timeless arm.

Pure vocabulary keeps source `ireg_in` (zero type or fresh shape plus a
present claim), `ireg_marked_ok` (nonzero type and absent claim), and
`ireg_link_ok` (zero type implies zero links, unsigned links ≤32767, type
in 0/1/2/3). The already checked fresh/type/bare definitions are reused.
The introduction theorem takes every native and pure component explicitly.
Pointwise projections and native arm exclusion may expose the assembled
resources without weakening the predicate.

The pointwise boot theorem takes a 32-bit inode, arbitrary full Dinode,
record/marker fragments, zero reference authority, zero observation
authority, an existing full registry row, region count/mirror halves,
filesystem link custody, and a conditional top fragment only at type zero.
It assumes exact link-ok and bare-at-type-zero facts, and preserves an
arbitrary frame. It initializes only the existing observation receipt via
its zero-lower-bound rule, then routes the record inside and marker outside
at type zero, or marker inside and record outside otherwise. The result is
the full actual slot and source `FsInodeRegion.out` at that same inode.
No reference, registry, record, link, top or world is newly allocated.

Generic Capacity and Names records expose the existing nine component
capacities and all ghost names. The concrete Link uses EscrowTokens37 and
exports no new registry extension. This closes the per-slot composition
boundary. Finite-region distribution, byte blocks, registry authority
coverage, region invariant allocation, pool payloads and whole icache boot
remain subsequent source obligations. The theorem is not a placeholder for
any of those resources.

All helper data/predicates reside in Defs, statements in Spec and proofs in
separate modules. Validation requires a full physical-origin audit traversing
opaque bodies, types and constructors, with the standard three axioms only.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
