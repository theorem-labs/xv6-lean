# Static kernel map complete peer review

Reviewer: OpenAI Codex logic audit agent, independently of the coordinator
who authored the implementation. Result: PASS for the declared static ghost
map scope; no correction requested.

I read all five modules (223 lines), their specifications and design, the
complete source `KMap.v`, and the classifier/map section of `KptPt.v` at paper
pin `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. All seven pure and five native
contracts are implemented, including absent-key cases. The interface review
is recorded separately in `kernel-map-static-interface-peer-review.md`.

`region_lookup` inducts over the finite interval. Its explicit upper bound
makes each inserted 27-bit key nonwrapping; equality and inequality of the
word keys are transferred through exact unsigned values. `lookup` uses the
actual **right-biased** ExtTreeMap union theorem and then proves the three
concrete source intervals disjoint. It does not import the source gmap's
opposite bias as an assumption. The result covers every VPN, including all
foreign and unclassified addresses. RX/RW case analysis, upper bounds,
positive-address reconstruction and text/data classification preserve their
exact source limits.

The native proof allocates the actual existing GhostMap at a fresh name,
retains its full authority and all persistent claims, and returns the supplied
frame. Claim lookup and exact-initial-authority identification use the same
capacity/name and the proved total map lookup. No existing-era name, physical
table, translation success, future mapping insertion or boot publication is
assumed or claimed.

The final definitions mark the ghost-only recursive region, initial map,
claims and authority noncomputable. This preserves their kernel definitions
and theorem types while avoiding an unused compiler unsafe recursion
companion. The final audit excludes **no** declaration.

Independent validation on the final frozen files:

- `tools/lake.py build Xv6.Kernel.KernelMapStaticLink`: GREEN, 655 jobs.
- Fresh physical-origin audit: all 79 declarations in all five modules,
  including private declarations, types, full opaque bodies and constructor
  dependencies. Only `propext`, `Classical.choice`, and `Quot.sound`; no unsafe
  or partial semantic dependency, zero exclusions.

Replay records are `/tmp/xv6-lean-research/KernelMapStaticPeerAudit.lean`,
`kernel-map-static-peer-audit.log`, and `kernel-map-static-peer-build.log`.
This proves and checks the static logical map, not its runtime installation
or whole-kernel safety.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
