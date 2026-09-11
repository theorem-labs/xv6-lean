# Independent shared three-read page-table walk review

PASS for all six KptTreeWalk modules. The Codex coordinator reviewed the
actual definitions, two public contracts, complete PTE/register folds,
pointer/leaf proofs and final native link separately from their author.
The source boundaries are the pinned raw PtTree walk and shared HartSKpt
ordinary PTE access already used by the reviewed lower layers.

The public PTE wrapper uses the actual read_pte program. Its checked
register prefix reaches the original complete request; the native shared
event chooses a permitted TSO-view word and returns the original four
control cells, reservation and persistent clients. The private boundary
argument is constructed from SupervisorPteRead.program_boundary, not
assumed by either public contract. The real residual handles the actual
successful response. Under the proved RAM/plain conditions, native memory
rules discharge the other cases without changing the model.

Upper reads recover the exact raw word from the nonleaf singleton family.
The actual pointer-validation plan retains all eager register reads and
continues at its real64-bit PPN with raw G accumulation. The final leaf
word is selected by the actual view and proved to be a KptLeaf A/D variant;
the actual validity, extension and permission plan supplies its result.
The composition spends exactly three memory guards, restores the same
cells/reservation/clients and returns all three actual receipts. No ordering
between the receipts is asserted. Each shared invariant opening is already
closed inside the single-read rule, so none spans another Sail event.

The target passed755 jobs. A fresh coordinator audit checked all47 physical
declarations, private helpers, complete types, opaque bodies and constructors
with exporting disabled. Only the three standard axioms occur, zero exclusions
and no unsafe/partial dependencies. Evidence: KptTreeWalkRootAudit.lean and
kpt-tree-walk-root-audit.log under /tmp/xv6-lean-research.

The explicit ambient hardware/PMP/PMA configuration still has to be obtained
from the caller's translation residue. Full A/D, TLB hit/miss, translated
instruction and boot-publication composition remain separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
