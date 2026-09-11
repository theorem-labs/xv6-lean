# Virtual scratch-stack ownership

The coordinator read the complete 645-line StackOwn.v at paper pin
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. This component ports the core
virtual stack definition/algebra at lines151–404 and tier weakening. The
physical mirror already exists as StackPhysical; its exact modular paStk
geometry is reused without changing existing proofs.

The stack contains an existential list of 64-bit scratch contents, its exact
length and the indexed separating conjunction of virtual KernelDatum words
at sp - 8*(i+1). Each word therefore retains the source mapping, positive
canonicality, RAM/tier pin and actual context byte/timestamp facts. Contents
may change when a split frame is rejoined; this does not weaken ownership.

Nine contracts give zero, append/split, one/two slots, two-slot frame with
the untouched deeper stack, tier weakening, and SP bounds/nonzero derived
from positive virtual ownership. They do not assume any concrete stack
layout. In particular, the bounds theorem rules out modular underflow at
the first slot by using its own positive-half address fact.

Context domination, migration/reindexing, base enumeration, boot conversion
and nonreturning reclamation are subsequent contracts. There is no context
reindexing implication or fresh scratch allocation hidden in this core.
The next mycpu adapter can use frame_two to obtain its real virtual save
slots while retaining the deeper stack at the original context and tier.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
