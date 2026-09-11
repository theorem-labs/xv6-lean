# Static kernel map interface peer review

Reviewer: OpenAI Codex logic audit agent, independently of the coordinator
who authored the interface. Result: PASS for the definitions/specifications
checkpoint; no implementation audit is claimed.

I read both KernelMapStatic modules, their design/status, the complete pinned
`KMap.v`, and `KptPt.v:460–469,795–903`. The three exact source intervals,
RX/RW classification, all absent keys and 49,154-entry total match. In
`region_lookup`, natural lower bounds supply the source nonnegative premise
and the explicit 27-bit range bound prevents key wrap. The representation
changes from association-list/gmap construction to interval insertion and
tree-map union; the required total lookup equality justifies it, including
union bias because the actual intervals are disjoint.

The native signatures use the existing map camera and discarded claims.
Allocation produces a fresh name with full authority and all claims while
retaining the supplied frame. Exact-M0 authority identification and persistent
fragment extraction match KMap. No physical table, existing-era allocation,
translation success or boot publication is assumed or claimed. No correction
is requested. The owner's interface build is GREEN at 410 jobs; the proofs
and their full dependency-cone audit remain the next checkpoint.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
