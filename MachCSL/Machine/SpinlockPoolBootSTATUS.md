# Arbitrary boot and power coverage for the spinlock annotation

BootProofs derives the initial lock/counter words and every initial cursor
from arbitrary actual BootFacts, including the generated reset's complete
Family certificate. PowerOnProofs preserves the full annotation invariant:
all old occurrences remain stale, exactly eight fresh harts are current,
and all eleven labelled forks erase to the actual powerFork. It consumes the
original BootShape, including retention of the current durable medium.

PowerOffProofs keeps all labels while incrementing the generation, making
all previous holders inactive without requiring an unlock. WorkerCoverProofs
provides the exact Covered conclusion for UART/PLIC/disk, stale harts and
power-off; PowerOnProofs supplies cover_power_on for every real boot witness.
These are pieces of complete Covers, not a completed all-run exclusion proof.

The full root-owned worker/boot chain builds505 jobs. BootProofs/PowerOnProofs
have31 declarations audited through every opaque body and referenced
constructor, standard three axioms only, zero exclusions. Independent
worker/off/cover review passed for18 declarations. Independent boot/on review passed; the complete five-module worker/boot
chain has49 declarations in the peer full-body audit, with zero exclusions.
See `docs/reviews/spinlock-pool-workers-review.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
