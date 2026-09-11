# Four-byte KPT memory independent review

PASS for the declared ordinary virtual-memory scope. Codex independently
read all 19 frozen Lean modules: five SupervisorMemOuter4, five
SupervisorWriteEA4, and nine KptMemory4 files, together with their design
and status. No implementation correction was required. The 21 hashes in
the owner's freeze manifest matched before and after review; no owner
files were modified.

The actual public programs are vmem_read_addr/vmem_write_addr with width
4, Load.Data/Store.Data and aq/rl/res=false. The transformed variants first
run the actual transform_effective_address. Generated VmemUtils.lean:
236–430 and Mem.lean:460–615 retain effective-privilege reads, page
splitting, translation, separate write-EA and value stages, callbacks,
metadata and error paths. Source correspondence was checked against
WpSconfMem.v:2512–2542,2781–2830,3196–3244 and the noff/intena operations
in ProofPushOff.v, including the source signed C.LW and full-owned stores.
These source rules include instruction, register, capability and cycle
wrappers; the reviewed layer correctly implements their lower memory
dependency only. GPR sign extension remains outside this component.

Four-byte geometry is exact. The virtual word supplies four-alignment;
its native accessor yields one actual mapped PPN, four original claims,
the physical context window and a value-polymorphic restoration wand.
Alignment transports through the mapping, and physical RAM membership
plus alignment proves the whole four-byte range. The page-split proof
gives (4,0), including offset 4092 and addresses congruent to 4 modulo 8.
No eight-alignment or caller-supplied range, physical word, PPN or successful
translation premise is added. The sparse mapping/claim and native context
resources fund the internal restoration wand; it is not a public
preservation assumption.

The native translation call uses KptAddress.nativeSpec with actual residue,
shared map ownership and the original reservation. Canonicality follows
from the virtual datum's positive address; the noncanonical raw program
branch remains in the factor and its native arm is contradicted by that
derived fact. Completion is derived from actual OutcomeFacts and the
explicit ambient configuration. Hit/miss and A/D alternatives retain
their original guard order and actual result-dependent scope. All
translation receipts survive, with exactly one further later and a
universally quantified view receipt for the ordinary data event. No
ordering between distinct receipts is invented.

Physical reads use the actual Load.Data readable-PMA and TOR checks.
The generic SupervisorFetchRead Boundary fold is reused as an ordinary
read-event adapter; it does not replace the data access class or assume
executable PMA permission. Writes use Store.Data writable-PMA and TOR
checks, then the actual HTIF query and plain present-payload request. The
request preserves all 32 bits, width 4, VA/translation/tag metadata and
nonexclusive flags. Register-plan widening proves membership in the same
combined footprint rather than duplicating any cell. The write-EA stage
retains its six actual register reads and pure write_ram_ea announcement;
it contributes no memory event or data later.

Raw factors preserve all translation and physical exception callbacks at
the original or offset virtual address. The read assembles exactly all
32 bits; the write extracts exactly all 32 bits. Actual false store
responses remain false. Native ownership, rather than a successful-response
input, discharges the successful data branch through the implemented
context read/write rules. Their concrete folds retain blocked-retry and
dead-generation handling in the actual machine WP. Loads preserve the
reservation returned by translation; stores clear it at the real write.

After the data event, the same nine control cells are partitioned back
into the five auxiliary cells and actual folded residue with its coherent
updated TLB. The same context, original tier and virtual address are
restored; loads retain arbitrary DFrac and value, while stores require
full ownership and return the new value. No initial allocation, new
camera, fixed-memory hypothesis or resource callback is hidden in the
public native Link. The explicit boot-PMA/HTIF and supervisor control
specialization remains a real precondition; this is not an equivalence
with unrestricted source sconf or a boot/resource-inhabitation theorem.

Independent validation:

- Fresh build of KptMemory4Link and SupervisorWriteEA4Link: 1,054 jobs passed.
- Strict physical-origin audit: all 255 declarations in 19 modules, including private/generated roots and complete types, opaque bodies and constructors. Only propext, Classical.choice and Quot.sound; no unsafe/partial dependency, Initial allocation dependency or excluded root.
- All 24 supplied ordinary-kernel fixtures passed: four-versus-eight alignment, page/RAM-end bounds, nonidentity PPN offsets, high payload bits, request size/plain flags, false/error tails, no-event EA and reservation behavior.
- Freeze hashes were compared again after the build, audit and fixtures; all 21 files remained unchanged.

Evidence: `/tmp/xv6-lean-research/KptMemory4PeerAudit.lean`,
`kpt-memory4-peer-build.log`, `kpt-memory4-peer-audit.log`,
`kpt-memory4-peer-checks.log`, and `kpt-memory4-peer-results.json`.
The peer audit directly rejects every unsafe/partial physical root; it
does not use a runtime-companion exclusion filter. The existing 24-check
file was rerun unchanged and its full fixture set read during review.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
