# Disabled Bare mycpu capability adapter

All six modules (Defs, Spec, Pure, Resources, Proofs, Link) are frozen and
build successfully: 892 jobs, including Proofs at 1.1s and Link at 863ms.
The reviewed public contract is unchanged. `actual` constructs its native
Spec from SupervisorBits.Spec and MycpuBare.Spec; `nativeSpec` discharges
both with the existing implementations. `registrySpec` reuses the complete
SupervisorBits registry and its existing BitVec1 camera at slot 44.
No new slot, name, physical authority or bit fragment is allocated.

The source boundary is SpecMycpu.v:31–47, ProofMycpu.v:59–318,
IntrDefs.v:649–653,2672–2699,3224–3229 and HartTp.v at xv6iris
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. This proves a disabled Bare
function resource adapter, not the full source sie_cap_gpr or sconf.

`footprint_counts` and `footprint_unique` prove the exact physical input
partition: 21 control keys, one mstatus and 31 GPRs, split into the
existing 28 cycle keys, eleven saved keys and fourteen framed keys.
`gpr_eq` ties the full pinned file to actual typed register cells and
x0's zero-value fact by kernel reflexivity. `partition` proves a reversible
native separation equivalence; neither direction duplicates ownership.
The mstatus and GPR cells are full; independent control shares retain
exactly the shares supplied to the underlying theorem.

`entry_config` derives MPRV=0, MXR=0 and SXL=2 from the complete source
MsFacts. One-bit MPRV not equal to one implies zero by finite kernel
checking. `wp_function` derives disabled SIE from agreement with the
actual off-token. TP=cpu is backed by the extracted full pinned x4 cell;
it is not an additional pure input fact.

`returned_agrees` uses only the existing function result's RA, saved
registers and stable TP facts on the keys it owns. `framed_entry` retains
all fourteen untouched GPR cells. `reassemble` restores the full pinned
software map, changing only a0/x10 and a5/x15 from owned returned values.
It does not read arbitrary unowned projections of the symbolic result.
The result retains all thirteen ABI software values, RA and the exact
CPU-address result, without adding TP to the ABI saved set.

The native fold invokes the actual fourteen-cycle hart theorem, with all
fetch, memory, retirement, clock and restart behavior unchanged. It
restores the same SIE half, SRET tied halves and off-token using the proved
unchanged physical mstatus, without a ghost update. Context, code, both
physical saved stack words and the cleared reservation return to the
genuine final continuation for every next tick. There is no per-step,
software-success or memory-access oracle, and no second register bundle.

A fresh full physical-origin audit checked all 202 declarations in the
six modules, their types, opaque bodies (`allowOpaque := true`) and
inductive constructors. Only propext, Classical.choice and Quot.sound
occur; there are no unsafe/partial semantic dependencies and zero
exclusions. No sorry, native_decide, bv_decide or custom axiom is used.
Independent coordinator source/proof review and a fresh202-declaration audit passed; see docs/reviews/mycpu-off-peer-review.md.

The remaining hardware/Bare configuration, actual physical stack/context
and text resources stay explicit. KPT/tier ownership, virtual free-stack
conversion, enabled handlers, source migration capabilities and the
preceding callable JAL wrapper remain separate. See the detailed design
in docs/design/mycpu-off-capability-adapter.md.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
