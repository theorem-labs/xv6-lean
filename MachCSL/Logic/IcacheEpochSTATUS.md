# Native inode observation epochs

IcacheEpoch{Defs,Spec,Proofs,Link} implements the complete observation receipt
section of pinned InodeRegion.v:1582–1711. The approved design is in
repository docs/design/icache-epoch-boundary.md. It uses actual LogEpoch
receipts and the shared MonoNat camera at separately supplied observation
names, with no new camera or allocation.

Names fixes the actual log epoch name, append-registry name, per-signed-inum
observation names and signed inode-start block. The observation-name function
is arbitrary; no injectivity or global initialization assumption is added.
Using the same supplied log names throughout enforces the source's gamma =
icfg_log tie. iblkOf agrees definitionally with the existing inodeBlock on
unsigned inum inputs, retaining signed Euclidean division for general keys.

The receipt retains the source BI implication and boot corner: if the record's
link count is zero, then its observation counter is still zero or a genuine
logged-block receipt exists at an epoch at least that counter. ireg_ep owns
the full observation authority, a log-epoch lower bound and that receipt.
nlz_obs is a persistent lower bound at the same observation name; ireg_ep
itself remains linear.

Intro consumes supplied observation authority at zero and mints only the
native zero log-epoch lower bound. Mint requires nonzero links and an actual
operation-epoch lower bound, updates the same observation authority to the
maximum, and returns its lower bound. Use requires zero links and a positive
observed epoch: real authority/fragment validity supplies observed ≤ counter,
which rules out the boot disjunct. It returns the same ireg_ep and an indexed
logged receipt at or after the observation. Two unrelated lower bounds are
never compared in place of the authority.

Record transport retains the source newly-zero-implies-previously-zero
condition. The deposit accessor retains the full counter authority in a linear
closure and accepts the new record's actual receipt. It does not produce that
receipt or justify a physical write. The Link constructs the native Spec from
LogEpoch.registryCapacity without an assumed invariant or callback.

Validation: the final four-module target passes 476 jobs. The independent
source and complete opaque/type/constructor review is recorded in repository
docs/reviews/icache-epoch-peer-review.md. Complete region-slot assembly,
operation-entry epochs, current-header membership, physical iupdate/commit,
boot initialization and all six whole-xv6 roots remain open.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
