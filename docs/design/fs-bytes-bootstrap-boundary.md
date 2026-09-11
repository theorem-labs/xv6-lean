# Complete native block/byte bootstrap boundary

Proposed owned prefix: `MachCSL/Logic/FsBytesBootstrap{Defs,Spec,PureProofs,
GrowProofs,Proofs,Link}.lean` and STATUS, with extra proof-only modules if
needed to keep elaboration bounded. No existing frozen definitions,
registry entries or root umbrellas change. The source is the pinned
`FsBlocks.v` complete mint sections 1424–1566 and 1709–1800, with the
underlying exact byte predicates, exception resources and nine-leg
invariant at 341–399 and 776–905. This implements the substantial native
allocation/distribution step that the existing region and bitmap bootstrap
currently take as an input.

The public Capacity is exactly `FsBytesInvariant.Capacity`: existing
FsBlockGhost cache/dirty/exception cameras at slots 39/40/41 and the same
signed Disk byte camera at slot 12. The existing six-field `FsBlocks.Names`
carrier remains unchanged. The supplied filesystem link/top names are
retained exactly; their resources and authority allocation remain with the
caller. No BioView, log-state invariant, disk physical-write claim or new
camera is introduced.

All keys remain arbitrary signed Int values. All maps and sets use the
existing extensional finite containers, including empty maps/sets and
negative home blocks. Define `homeMap C home` and `outsideMap C home` using
complementary decidable key filters, a same-domain `valueMap C Bv` mapping
each present key to `Bv key`, and `cleanMap C` mapping each present entry to
false. The map filters do not manufacture absent entries. Definitions also
name the actual block-resource ledger and final result bundle below, to
keep repeated 1024-element predicates out of proof-mode normalization.

## Three native allocation contracts

1. **`byte_map_grow`, FsBlocks1424–1504.** For arbitrary existing byte map
   `L0`, old home set `h0`, new block map `C`, and fixed byte ghost name `gL`,
   assume exactly: every C entry is 1024 bytes; each key of C lies outside
   h0; and `bytes_dom L0 h0`. From `Disk.mapAuth gL L0`, produce by native
   basic update an existential byte map L with `bytes_dom L (h0 ∪ dom C)`,
   `bytes_tie L C`, the same-name full authority at L, and the full concrete
   `FsBlocks.block gL b bs` ledger over C. Preserve an arbitrary supplied
   frame. This updates the supplied authority; it does not replace it with
   a fresh authority. A checked implementation can bulk-insert the existing
   guarded `FsDurBytes.flatten C` after proving its byte-domain disjointness
   from L0, then use the existing native byte-ledger/block-ledger equivalence.
   The full-block premise discharges the flattening order guard; no
   malformed-overlap enumeration assumption is introduced.

2. **`fs_bytes_alloc`, FsBlocks1514–1565.** For a supplied cache name gc and
   cache map C, committed value function Bv and exception set X, assume
   exactly the four source premises: C entries have length 1024; Bv has
   length 1024 on dom C; X is a subset of dom C; and each C entry outside X
   agrees with Bv. Consume the supplied native cache-half ledger over C.
   Allocate a fresh same-world logged byte name gL and exception name gX,
   build the actual invariant at fsbN with home dom C and fixed Bv, and
   return the full exception handle at X plus a full byte-block ledger
   at Bv for every C key. Preserve the arbitrary caller frame. Other
   filesystem names remain untouched. The invariant consumes the byte
   authority and the supplied cache halves, retaining the raw C values;
   its byte view uses Bv, with agreement imposed only outside X.

3. **`fs_alloc`, FsBlocks1738–1800.** Given fixed link/top names, arbitrary
   covered map L0, home set, committed value function Dv and exception set
   X, assume exactly the five source premises: all L0 entries full;
   home subset dom L0; Dv full on home; X subset home; and L0/Dv agreement
   on home outside X. From an arbitrary caller frame, allocate actual
   cache, dirty, byte and exception names under a native fancy update and
   return the same frame and all of the following resources:

   - pure equality of the resulting filesystem link/top fields to the
     supplied names;
   - full cache authority at L0;
   - full dirty authority at cleanMap L0;
   - actual byte invariant over the named home set with fixed Dv;
   - full exception handle at X;
   - for every covered L0 entry, its actual mclean payload (cache half plus
     dirty half at false) **and** the second dirty half at false;
   - full exclusive byte blocks at Dv for the home-filtered entries;
   - parked cache halves at the raw values for every outside-home entry.

   Each cache element is split exactly into machinery and parked halves;
   only the home parked halves enter the byte invariant. Both dirty halves
   remain explicit in the output. No affine omission of a client-side
   column is accepted as completion. Home is supplied as a set, not
   replaced with a hardcoded initial-image interval; in source callers it
   is coverage minus the actual log region.

The generic filter split and domain-equality laws at 1709–1730 are included.
Their proofs establish exact complementary coverage and resource separation
for arbitrary finite maps, not an unchecked enumeration partition. The
value-map lookup/domain bridge establishes that byte ownership after the
mint is indexed by the original C domain despite changing each payload.

## Operational meaning and next integration

This is fresh *logged-view* ghost allocation in the existing world, exactly
as the source era mint permits. It is not `FsDurSnapshot.Initial`, does not
mint a new Iris world, and does not claim that pure premises constitute a
linear once-only authorization. Existing physical disk authority and any
other caller resources remain framed unchanged; framing alone does not
prove raw or committed content equals the physical disk. The later
FsBoot/FsCrash caller must supply that actual source relationship.

The source exception set can be nonempty at PowerOn. This boundary returns
the full recovery handle, not a seal; a clean-header specialization may
separately spend the empty handle with the already proved native seal rule.
Recovery installation, log/bitmap/config invariant assembly and whole
filesystem initialization remain subsequent steps. Completing this scope
removes the currently supplied block/byte-allocation legs needed by those
steps, rather than merely repackaging their predicates.

Definitions and Spec are submitted first for review; native proofs follow
approval. Final validation builds every owned module and checks all logical
physical-origin roots, private/generated declarations and transitive opaque
bodies, types and constructors. Only the standard three axioms are allowed,
with no unsafe/partial logical dependencies or Initial allocator calls.
The final STATUS will inventory direct callers of these source mint rules
and distinguish allocation from supplied-authority extension.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
