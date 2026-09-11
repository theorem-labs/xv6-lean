# Two-tree TLB provenance during a SATP-switch window

Four modules implement the source PtTree.v:1999–2112 two-tree coherence
relation and its seven transport/fill/update laws, plus current-side
injection, symmetry and equal-tree collapse. Each occupied slot may come
from either tree independently. A vector can contain a mixture; neither
tree is assumed to be the provenance of every entry.

The exact existing CacheOf relation retains installing VPN, hash collision,
raw upper words, ASID, global bits, leaf A/D variant and physical PTE origin.
Canonical transport and A/D updates work on either side. Fills use the
actual fixed64-entry vector update, retaining other slots even when the
query differs from the installing VPN but shares its hash. Leaf validity,
Napot and PBMT facts after an A/D update are derived by the underlying
canonical proof, not additional caller preconditions.

Defs/Spec are separate from proofs; nativeSpec supplies the proved native
single-tree laws. Build passed453 jobs. The owner audit checked29 physical
declarations and their full type/opaque/constructor cones with exporting
disabled: only propext, Classical.choice and Quot.sound, zero exclusions,
no unsafe or partial dependencies. Independent source review and a fresh29-declaration audit passed; see
docs/reviews/tlb-window-peer-review.md.
Evidence: TlbWindowAudit.lean, tlb-window-build.log and tlb-window-audit.log
under /tmp/xv6-lean-research.

This proves the pure provenance rules required by the source switch window.
It does not execute SATP writes, flush a TLB, allocate either physical tree,
or implement the complete two-tree translation WP. Those remain open.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
