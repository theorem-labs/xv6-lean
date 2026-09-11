# Independent TSO views review

Reviewed `MachCSL/Logic/TsoViewsDefs.lean`, `TsoViewsSpec.lean`,
`TsoViewsProofs.lean` and their status record against `TsoGhost.v` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476` and native Iris's
`BI/Lib/MonoNat.lean`. No correction required for the declared partial scope.

The total `Nat → MaxNat` carrier preserves every source agent, including
non-CPU agents. Authority owns both authoritative and same-valued fragment;
receipts contain both the per-agent lower bound and log-length lower bound,
with the exact pure-zero alternative. All section 1, 3 and 4 source laws are
represented, including persistent fragments, authority update, zero minting,
lower-bound weakening, validity, and receipt acquisition retaining both
authorities. Generalization of `llb_get`/`llb_valid` to arbitrary native
`DFrac` is justified by the reused Iris laws; full-fraction source signatures
remain direct instances. No stronger monotonicity premise was added.

The four-slot extension preserves the previous two slots. New membership
certificates, including the old ledger capacity at the extended family, are
concrete checked values. A single shared mono-nat slot serves independently
allocated runtime names; it does not manufacture a second ambient generation
capacity. Native `MonoNatG.name` is not used by its explicit-name ownership
and allocation definitions, so the temporary name-0 allocation adapter does
not restrict fresh allocation to 0. The separate contract imports definitions
without importing its proof implementation. No machine tracking or adequacy
claim is made by the exported contract.

This review inspected source and elaboration-facing signatures independently;
it did not repeat the owner's whole-namespace axiom audit or full build. The
owner reports both green and standard-three-axiom-only. Remaining log/dirty,
metadata, era, interpretation and adequacy scope is stated accurately.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
