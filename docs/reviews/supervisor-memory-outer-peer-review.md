# Independent review: outer supervisor memory wrappers

Reviewer: the Codex Lean-logic agent, independent of the coordinator who
implemented this slice. **PASS for the stated outer physical-memory scope**;
no correction requested. The final successful read residual explicitly
reduces `MemoryOpResult_drop_meta` and the pure bind before the continuation.

I read all five frozen SupervisorMemOuter modules and the design, then
compared the actual generated `Mem.lean:460–609`,
`SysControl.lean:222–225`, and native checked read/write interfaces. Source
comparison used pinned xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`,
particularly `HartSMem.v:751–804` (`swp_mem_read_S`) and `3036–3096`
(`swp_mem_write_value_S`), with the immediately following virtual-store
composition at 3098–3253 to check the scope boundary.

The actual prefix reads mstatus then current privilege. The concrete
Supervisor/MPRV-zero hypotheses discharge effective privilege using the
existing proved native model equation. The generic prefix also handles
instruction fetch without requiring MPRV zero. Other status bits are
unconstrained; no SXL, MPP, reset snapshot, or translation regime is hidden in
the outer read/write contracts.

The two privilege cells and the four physical permission cells are disjoint
register keys, independently fractional, and held as separate linear
resources. `RegisterPlan.fold` consumes and returns only the privilege
footprint while framing physical and context resources. The subsequent
checked-memory rules frame and return those privilege cells. There is no
full register assertion, aliasing-induced duplicate ownership, or new ghost
camera. All native generation/dead-thread behavior is inherited from the
actual leaf rules, and each real register or memory event remains separately
interruptible.

`read_meta_eq` retains both actual callback arms and every success/error
value. The callbacks are pure in the pinned generated model, and the
right-unit equality removes only that pure wrapper. `read_supervisor` keeps
the generated metadata-dropping function; it does not assume success to
prove a program equality. In the native theorem success comes from the
context-owned checked read, for every permitted selected read view. The
final result is precisely `Ok word`, with unchanged context/word and a
selected-view lower-bound receipt. The wrapper has no exclusive read and
introduces no reservation acquisition or clearing; an existing reservation
fragment may be framed.

The write factorization keeps the actual effective-privilege reads and uses
the independently proved full callback equality. The native checked-write
rule supplies the new context word, cleared own reservation and the ordinary
write receipt, with actual authored log append/full heap metadata handling
paid by the underlying context rule. Blocked writes keep the retry and old
resources. This does not assert a single uninterrupted state transformation
for the entire outer wrapper. The pure wrapper equality retains its error
values; the owned native rule establishes the successful continuation.

The source factors its outer read/write lemmas through subordinate checked
access obligations. These public native rules construct and discharge those
obligations using the concrete context rules. Neither a software/access WP
nor a state-preservation oracle remains a premise. The scope is actual
`mem_read`/`mem_write_value` with a physical address, not `vmem_read` or
`vmem_write`. No virtual translation, address transformation, canonical PTE
pin, page-table credential, or `mem_write_ea` announcement proof is claimed.
The last is a separate real register-read prefix required by later store
composition even though `write_ram_ea` itself is pure unit.

The coordinator's final target build passed **544 jobs**. My fresh independent
physical-origin audit checked all **49 declarations** in all five modules,
including private helpers, transitive types, bodies with
`allowOpaque := true`, and inductive constructors. Only `propext`,
`Classical.choice`, and `Quot.sound` occur; no unsafe/partial logical dependency
and zero excluded runtime companions were found. Evidence:
`/tmp/xv6-lean-research/SupervisorMemOuterPeerAudit.lean` and
`supervisor-memory-outer-peer-audit.log`. The final changed read residual was
read before this audit. Whole generated-model/Rocq correspondence remains a
separate documented project limitation.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
