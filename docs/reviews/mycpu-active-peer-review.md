# Independent active-hart preparation review

Read all five MycpuActive modules against complete generated
Step.lean:321–396 and the source disabled-SIE progression structure.
`factor` is unconditional and preserves all interrupt, fetch, decoder,
landing-pad, extension and execution outcomes. It follows actual Free/ExceptT
structure, with kernel-checked reassociation and case analysis.

The decoder plan transfers the existing checked certificates only when
each populated snapshot register is covered and owned. Memory, missing
snapshot values and writes cannot pass this transfer. The same fourteen
cells pay the actual privilege/interrupt/fetch/post-fetch accesses;
interrupt mip and external pins remain independent universal reads.
Actual exact decoder configuration premises remain unchanged.

The preparation prefix explicitly reads ELP and requires ELP zero, queries
Zca again for compressed instructions, reads PC and writes nextPC using
the actual instruction size. Fetch-window width is not substituted.
The residual retains exactly one ExecuteAs redirection and the actual
Step_Execute bits; a second redirect result is returned verbatim.

`Prefix.fold` is an ordinary native residual-body bind rule with its
continuation obligation visible. The Spec claims only factoring, dispatch
and preparation and is constructed without a body-correctness hypothesis.
No standalone active-step/function safety or cold-supervisor initialization
is claimed. Widening preserves the shared footprint without duplication.

A fresh independent complete physical-origin audit passed all123 logical
declarations, private matchers and opaque values/types/constructor fields.
Standard three axioms only, no runtime exclusions or unsafe/partial logical
dependencies. Command: `PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py
env lean /tmp/xv6-lean-research/MycpuActiveAudit.lean`.
Evidence: `/tmp/xv6-lean-research/mycpu-active-peer-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
