# Independent durable footprint-carving review

Reviewer: coordinator OpenAI Codex, reviewing all seven frozen FsDurAlloc modules against the pinned source FsDurAlloc.v definitions and guarded obligations. Result: **PASS**.

All six source slot constructors and their addressing rules are preserved, including signed inode division/remainder, total missing-node lookups, conditional empty indirect/free-pool slots and pool block zero. The missing-node default intentionally has empty record addresses and indirect entries, distinct from the shaped zero inode. Kernel checks record its twelve-byte raw record, missing data, used pool and zero-pool behavior.

The exact family includes every mapped inode record, held data-map key, indirect slot and signed in-range pool block. Membership equivalence and uniqueness hold for arbitrary states. Enumeration order is not claimed equal to Rocq map order. All pure range, submap and separation facts are derived from Snapshot.Bytes: exact block lengths, record slices, nonzero/in-range data slots, metadata exclusion, used/free disjointness, same-node slot injection and cross-node disjointness. Empty slots are handled separately rather than assumed nonempty.

The native carve first proves that the disjoint selected union is precisely the separating conjunction of its slot ledgers, then cuts it once from the supplied whole map. It returns the exact whole-minus-selected difference and arbitrary frame. The actual Disk12 registry wrapper additionally preserves the original authoritative whole map and permits whole to strictly extend the flattened disk map. No replacement authority or fresh byte name is allocated.

Fresh coordinator audit passed all246 declarations and full type/body/constructor cones, standard three axioms only, zero exclusions and no unsafe/partial dependency. Owner build passed438jobs. Evidence: fs-dur-alloc-root-audit.log in the research directory.

Regrouping these slots into native FsState and allocating the durable snapshot remain separate work. The guarded flattening correspondence still requires its documented length premises, here supplied by Snapshot.Bytes.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
