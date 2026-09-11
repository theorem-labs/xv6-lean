# Independent supervisor TLB-hit factor review

PASS for all six Sv39Hit modules. The Codex coordinator reviewed the
definitions, thirteen contracts, actual generated-program factorization,
register plans and native folds separately from their author.

The raw factor retains permission failure, the actual update program and
all three update responses. The supported KptLeaf specialization proves
permission success from the leaf's actual flags and extension bits. Cached
no-update performs no MENVCFG read; the other branch reads its actual gate.
The enabled remainder is still the real exclusive-read/check/conditional-write
program. An error stays an error, and a false conditional write stays the
original internal_error event. Neither is turned into success.

Resume changes the TLB only for Ok(Some word). Its actual read/write plan
retains all other vector entries and the original entry's PPN, PBMT, tag,
ASID, global flag and PTE origin. In particular, it does not recompute the
returned PPN from an arbitrary supplied response word. Coherence preservation
requires the derived A/D variant only on that Some branch. The public native
head and resume rules own exactly the MENVCFG fraction and full TLB cell.
Their remaining enabled-memory WP is explicitly open in this layer; it is
not advertised as a complete hit theorem or supplied successful callback.

The target passed496 jobs; seven additional kernel branch checks passed.
A fresh coordinator audit checked all80 physical declarations, full types,
opaque bodies and constructors with exporting disabled. Standard three
axioms only, zero exclusions and no unsafe/partial dependencies. Evidence:
Sv39HitRootAudit.lean and sv39-hit-root-audit.log under /tmp/xv6-lean-research.
Complete shared hit composition and lookup-to-residue integration remain.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
