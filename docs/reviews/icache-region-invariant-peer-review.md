# Inode-region invariant independent review

PASS for the exact source invariant package and final allocation step.
The root reviewer read all four physical modules, the design and the source
`InodeRegion.v:3239–3280`, together with the existing native region body,
logged-byte row and top-registry definitions.

`ireg_reg` and `ireg_inv` use the actual Iris invariant and the same complete
body, with the real unsealed or sealed byte row and top invariant. Native
projection/sealing rules preserve the actual empty-exception seal. The
allocation theorem consumes the supplied full body through native
`inv_alloc`; it preserves the provided byte/top resources and caller frame.
It neither constructs the earlier slot clients nor claims full boot allocation.

Derived capacities and names structurally share the byte, top and
transaction ghosts. Link equalities check Disk12, FsTop25, LogTx33 and
record27 within the unchanged registry through41. The generic start is
independent of the epoch's start field, as in the source; image composition
must use the separately checked literal tie. No equality premise is hidden.

Fresh root audit `IcacheRegionInvariantPeerAudit.lean` passed all **84
logical declarations** in the four physical modules, including complete
transitive types, opaque bodies and datatype constructors. Standard three
axioms only, zero exclusions, no unsafe/partial or initial-snapshot
allocation dependency. Evidence:
`/tmp/xv6-lean-research/icache-region-invariant-peer-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
