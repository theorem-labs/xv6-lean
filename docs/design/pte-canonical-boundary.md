# Native PTE canonical byte-family boundary

This pure boundary ports `PtAdBits.v` and `PtTree.v:929–1094` at the pinned
paper source. `setAD` is the exact generated `updateSubrange` plus generated
A/D flag updater expression, and `nonleaf` calls the generated classifier.
The canonical word clears exactly bits 6 and 7. No Sail effect or validity
branch is replaced by a pure oracle.

The native finite byte family uses the existing extensional `Tso.ByteSet`.
Interior PTEs permit eight singleton bytes; leaf PTEs permit exactly the
four A/D variants at byte zero and singleton bytes at the other seven
positions. The public contracts prove exact word reconstruction for an
interior read, canonical equality for every family read, and family
preservation for a leaf read or write-back. The latter is the payload
condition needed by the existing native pinned-store resource update.

The generated `update_PTE_Bits` theorem quantifies over every access kind,
including prefetch and cache-management cases, and retains its actual
`some` premise. The write-back contract separately requires the source
leaf condition. Neither the hardware walk nor the reservation/exclusive
write success branch is claimed by this pure boundary.

Proofs use Lean's kernel-checked bit projections and byte reassembly.
The separate Spec records the source obligations; Bits and Proofs discharge
them and Link exposes the native implementation. Validation builds each
module and audits every physical declaration, transitive type, opaque
body and datatype constructor. Only the standard three axioms are allowed.
The larger KPT invariant, TLB consistency, real walk events and conditional
A/D store proof remain subsequent dependencies.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
