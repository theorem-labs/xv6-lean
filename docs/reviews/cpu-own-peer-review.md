Independent review: exact disabled per-CPU ownership

Read all six files and the actual source CpuOwn/IntrDefs/ProcGeom resource
boundary. The noff and intena fields retain four identity virtual/context
bytes each; proc retains its full eight-byte word. Count, held-lock level,
CSR names and fractions agree with the existing actual era capacities.
The active source interrupt count has no restore payload; stale prose is
not used to invent one. Positive nesting with saved enable true remains
possible, while zero-depth agreement with the disabled arm forces false.

The word4 accessor funds four replacement-byte mapping closures internally.
Full noff ownership establishes exclusivity even across different contexts.
Boot introduction consumes all actual field, SIE, held-authority and CSR
resources. Count-only equivalences reindex the eighth without changing
physical memory. All accessors return exact reconstruction obligations.
The existing registry slots 26/44 are reused with explicit name agreement.

Validation: 903-job build and fresh independent strict audit of all 137
physical declarations in six modules, complete types/opaque/constructor
cones, standard three axioms only, no unsafe/partial dependency and zero
exclusions. No enabled capability, migration, boot allocation or push_off
execution theorem is claimed. Review passed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
