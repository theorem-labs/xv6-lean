# Actual Bare virtual eight-byte read

Root-owned five modules Defs/Spec/Plan/Proofs/Link. Actual `vmem_read_addr`
ordinary Data eight-byte read is proved through `program_boundary` and native
`wp_read`/`nativeSpec`. Supporting `outer_boundary` and `translate_boundary`
retain actual Sail callbacks and exception/result wrappers. The seven-cell
footprint owns status, privilege and satp once across repeated real reads.

The actual page split reuses the kernel-checked arbitrary aligned-word geometry
in SupervisorBareWriteGeometry; no RAM/no-wrap assumption is added to that
lemma. Public native WP derives alignment from its supplied context-word resource.
The actual mode/effective/translation/physical prefix pays fifteen register
reads, one real ordinary read event, exact whole-word assembly, and the genuine
result constructor. All tag-success and error-Exit tails remain checked.
Native folding returns same7cells/runningcontext/word and actual view receipt.

Configuration premises explicitly require Supervisor/SXL2/Bare/MPRV-clear,
matching readable PMA, TOR RAM and HTIF disabled. No new camera, byte allocation,
state-preservation callback or read-value oracle. Base register pointer formation,
vmem_read, fetched LOAD, KPT/source stack and whole function correctness remain
subsequent layers; this is only the explicit Bare virtual-address access tier.

Validation: `PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py build
MachCSL.Logic.SupervisorBareReadLink` passed 548 jobs. Full physical-origin
opaque-value/type/constructor audit passed all 57 declarations, standard three
axioms and zero exclusions. Independent review passed; see
docs/reviews/supervisor-bare-read-peer-review.md.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
