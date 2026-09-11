# Bitmap and inode-decoding peer review

Decision: pass for the bounded source resource and decoding lemmas. The coordinator read all seven Lean modules and the exact IcacheBoot image predicates/decoding, FsCfgSnap snapshot bridges, BitmapInv.bitmap_res/open/timeless and FsStateBitmap.free_pool_intro source boundaries.

The bitmap resource is the existing freeBitmapAt predicate at the caller's logged byte name. Snapshot construction uses the actual bitmapSpent ownership, derives the encoding from the restricted snapshot map, and obtains disjointness from the metadata-used clause. The generic pool bridge preserves signed size, block zero, empty cases and existential block contents. It introduces no allocation, coverage clause or invariant oracle.

The inode decoder preserves the source's total double lookup, signed division/modulo and empty-address default. The explicit negative-one law catches the non-obvious row-0/slot-15 behavior. The six region predicates are retained separately: free link count, short link count, supported type, named count equality, bare free records and named record equality. Bare constrains size and all thirteen addresses, independently of type and links. The snapshot bridge keeps exact byte encoding, sixteen-record well-formedness, rounded region width and 32-bit bound premises; it derives facts from the same snapshot records.

Fresh coordinator audit: all 22 bitmap and 27 inode-decoding physical declarations pass, in the combined 177-declaration audit over 14 reviewed modules. Types, opaque bodies and inductive constructors are traversed; initialization-only allocation dependencies and unsafe/partial logical dependencies are rejected. These seven modules have no runtime exclusions and use only the standard three axioms. Evidence: /tmp/xv6-lean-research/BootstrapContextPmpPeerAudit.lean and bootstrap-context-pmp-peer-audit.log. Agent builds: 454 and 255 jobs respectively.

This does not construct the bitmap invariant, inode-region slots, reference escrow or full filesystem bootstrap. The native allocation prelude is the next bounded source layer.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
