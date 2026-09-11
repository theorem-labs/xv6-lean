# Supervisor outer memory access

Frozen five modules: Defs, Spec, Plan, Proofs and Link. Native `wp_read` and
`wp_write` wrap the actual eight-byte mem_read/mem_write_value with their two
effective-privilege register reads and the actual metadata/callback behavior.
`effective_plan`, `read_meta_eq`, `read_factor`, `read_supervisor`, `write_factor`
and `actual` connect exact generated code and native resource rules.
Two fractional status/privilege cells supplement four physical permission cells;
reads return the same context word, writes return the new full word and cleared
reservation, with actual view receipts and both register bundles preserved.

Validation: `PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py build
MachCSL.Logic.SupervisorMemOuterLink` passed 544 jobs. Independent full source
review and all-49-declaration type/opaque-body/constructor audit passed; only the
standard three axioms, zero runtime exclusions, no unsafe/partial logical cones.
See docs/reviews/supervisor-memory-outer-peer-review.md.

Assumptions are explicit Supervisor/MPRV-clear values, actual matching PMA grant,
TOR RAM range, HTIF disabled, and supplied native generation/context/register/word
resources. No new camera, initial allocator or semantic oracle. Generic effective
fetch prefix does not require MPRV clear. mem_write_ea, virtual address formation,
Bare/KPT translation and full instruction/function composition remain open.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
