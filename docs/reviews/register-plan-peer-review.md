# Independent fractional register-plan review



Reviewer: independent `lean_logic_audit` Codex agent; the coordinator wrote
the reviewed modules. All six `RegisterFootprint{Defs,Spec,Proofs}` and
`RegisterPlan{Defs,Spec,Proofs}` files were read completely. **PASS**; no
production changes requested.

The footprint is an actual finite list of register/fraction pairs.
`read_access` extracts exactly the requested pair and returns a wand that
restores the original list, without requiring unique keys. This permits
split fractions or repeated discarded assertions without manufacturing an
additional token. `write_access` requires full ownership and key uniqueness;
the proof uses that uniqueness to show every other listed register is
unchanged by the dependent register-file update. `cells_append` preserves
the separation structure. No fixed 178-register ownership premise remains.

`RegisterPlan.Plan` describes finite segments of the actual free Sail tree.
Owned reads keep the exact listed fraction; unrestricted reads quantify
all values independently; writes require a listed full cell. `bind` and
`mono` preserve those cases. The native fold applies the existing proved
single-event read/write/read-any WPs, closes each restoration wand at its
own node, and places the remainder under the native later. The generation
certificate is duplicated only through its proved persistence. The final
WP continuation is the caller's real continuation, not an assumed software
correctness rule or whole-instruction atomicity premise.

The symbolic `RegisterFile` indexes ownership only for listed registers.
An unlisted component is not a claim about the actual hardware register;
a `readAny` result is universally quantified and does not update that
symbolic component. The fold's conclusion correctly returns only the same
footprint and its symbolic postcondition. Future consumers must retain
this interpretation rather than treating `Returns` as whole-register-file
agreement. The module itself makes no such whole-file claim.

The coordinator reported builds green at 321/423 jobs. A fresh independent
physical-origin audit checked all **57 logical declarations in six
modules**, traversing opaque theorem bodies and inductive constructors.
Only `propext`, `Classical.choice`, and `Quot.sound` occur; no unsafe or
partial declaration occurs in any logical dependency cone. One generated
runtime companion for total recursion was excluded as a declaration root;
the corresponding logical function and its full cone were checked.
`RegisterFootprint.actual`, `RegisterPlan.fold`, and `RegisterPlan.actual`
were also checked individually with `#print axioms`.

Evidence: `/tmp/xv6-lean-research/RegisterPlanPeerAudit.lean` and
`/tmp/xv6-lean-research/register-plan-peer-audit.log`. Memory boundaries,
SIE/timer invariant access, translation, and a supervisor function WP remain
outside these register-only modules.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
