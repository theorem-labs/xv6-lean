# Independent native durable snapshot review

Reviewer: coordinator OpenAI Codex, reviewing all five frozen FsDurSnapshot modules against pinned FsDurSnap.v:807–826 and the initial allocator in FsDurAlloc.v. Result: **PASS for native snapshot definitions and designated initial allocation**.

fsSnap has exactly the six source legs: byte authority over a submap of the flattened committed blocks, full top-map authority, every top fragment, native full FsState, a root-inode ticket, and the pure Shape fact. Pdur hides the three names and state exactly as in the source. Neither definition silently adds Snapshot.OK or equality between the authoritative bytes and the entire committed map. The timeless and projection laws follow these exact resources.

Initial allocation creates a fresh snapshot byte name at the existing Disk camera, then allocates the valid root-slack link family and top resources. It assembles the supplied snapshot byte ledger into native FsState, retaining the exact uncarved remainder and caller frame. The weaker existential Pdur corollary may discard that remainder through the source's affine logic. Registry wrappers preserve the original physical or finite-map disk authority unchanged; this framing fact alone is not a physical-disk/snapshot equality theorem.

The initial-only namespace is documented usage discipline, not a linear permission or once-only enforcement mechanism. Integration must audit its callers and use source-instance transport for runtime epochs. Arbitrary malformed-map cross-language predicate equivalence also remains outside the guarded flattening correspondence; the initial constructor obtains full block lengths from Snapshot.OK.

The owner corrected the durable update's modal parentheses before review, so the update contains both Pdur and the returned frame. Explicit notation-free modal checks passed. Fresh coordinator audit passed all41 declarations and complete type/body/constructor cones, with standard three axioms only, zero exclusions and no unsafe/partial dependency. Owner build passed463jobs. Evidence: fs-dur-snapshot-root-audit.log in the research directory.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
