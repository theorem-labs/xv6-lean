# Fractional register footprints and native prefix folding

Six modules implement finite register resources and a fold for register-only
segments of the actual free Sail tree. RegisterFootprint exposes an arbitrary
list of (register, DFrac) pairs over the existing dependent native register
camera. Read extraction returns exactly the same token and restoration wand.
Full-write restoration requires unique keys; every other cell is framed by
the actual dependent register-file update. Append is a separating equivalence.
No allocation or fixed full-register-file ownership is required.

RegisterPlan retains a symbolic register table only to index the listed
resources. Unlisted components assert nothing about the actual hardware.
Owned reads select the value backed by a listed token; readAny quantifies
every value independently, and does not assert agreement with the unlisted
table component. Writes require a full listed cell. The well-founded plan's
bind and monotonicity laws compose exact generated continuations.

The native fold invokes the already proved RegisterWP single-node rules
directly, retains each fractional/discarded token, and restores the finite
footprint after every write. Each event consumes an actual machine step and
places its continuation under the native later; death on generation change
is handled by those same rules. The terminal caller continuation is an
ordinary native WP. No register-rule contract or software-correctness callback
is assumed. Memory, fences, timer invariant access and translation remain
separate event boundaries and are not silently dropped.

This is a Lean proof-engineering adapter for the source's fractional register
partition (RiscvPtsto and HartRegNode), needed because EventPlan's existing
178-full-cell fold cannot consume the source supervisor capability. It is
not a replacement resource definition or a completed supervisor function WP.

Builds pass 321 jobs for RegisterFootprintProofs and 423 for RegisterPlanProofs.
The independent lean_logic_audit agent read all six files and checked all 57
physical-origin logical declarations, opaque theorem bodies and constructor
fields. Only the standard three axioms occur. One compiler companion of safe
total recursion is excluded as a root, and no unsafe/partial declaration
occurs in the logical dependency cone. See
[the peer review](../../docs/reviews/register-plan-peer-review.md).

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
