# Shared-Sv39 mycpu memory bodies

FROZEN: all fourteen pure and two native contracts are proved in eight
modules: Defs, Spec, Pure, Factor, Resources, Rules, Proofs and Link.
`nativePureSpec`, `nativeSpec` and `registrySpec` are constructed from the
actual generated Sail programs and the existing native KptMemory rules.

The four actual image positions are 1/2/10/11: C.SDSP RA/S0 and C.LDSP RA/S0.
Stores read the source before SP; loads perform the actual target-register
write after the data event. Raw STORE Ok false still returns Retire_Success,
and raw LOAD/STORE Err tails are preserved. Native RAM ownership discharges
the actual successful response internally.

One fifty-key cycle/GPR packet supplies seven distinct borrowed cells and
forty-three framed cells. The hidden SATP/TLB/PMP registers occur only in the
source KPT residue. The load result replaces only software GPR index1/8;
SP, TP, the other GPRs, controls and source SIE/SRET/off fragments are restored.
MPRV/MXR/SXL facts come from native msOwn. Config retains the actual explicit
Supervisor/PMA/HTIF/MENVCFG facts. No physical word, translation-success
premise, memory/body WP oracle, new camera or duplicate register packet is
required.

The virtual-word rule retains every native hit/miss and A/D guard followed
by the data guard, evolved reservation and all receipts. Its two-slot rule
retains the unselected full virtual word and arbitrary caller frame. The
final returned-body continuation is a genuine WP premise. Actual fetch,
cycle composition, full source sconf/sie_cap_gpr and the complete mycpu
function are outside this layer.

Validation:
`PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.MycpuKptMemoryLink`
passed 1,056 jobs (Proofs 1.5 s, Link 875 ms). The fresh physical-origin audit
checked all 178 declarations in eight modules and their complete
opaque/type/constructor cones: only propext, Classical.choice and Quot.sound;
no unsafe/partial dependencies and zero exclusions. Research logs are
`mycpu-kpt-memory-build.log` and `mycpu-kpt-memory-audit.log`.

Source pins, exact generated/source line references and resource mapping are
in `docs/design/mycpu-kpt-memory-boundary.md`. No frozen dependencies,
generated model files, umbrellas or registries were edited.

Coordinator final peer review also passed: all implementation files read and
a fresh full audit checked 178 physical declarations through types, opaque
values and constructors, with standard axioms only and zero exclusions.
The corresponding peer report is in docs/reviews.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
