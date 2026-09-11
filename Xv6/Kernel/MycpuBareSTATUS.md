# Complete Bare mycpu native function CPS

Eight frozen modules: MycpuBare Defs, Spec, Geometry, State, Reference,
Config, Proofs and Link. `wp_function` and `wp_hart` implement both fields
of the independently stated `Spec`; `nativeSpec` discharges the complete
native component contracts for any existing MachineInterp capacity. No
new camera, name, allocation, instruction interpreter or generated-model
change is introduced.

The proof composes all fourteen actual `MachCSL.Machine.cycle` rules for
the pinned function at 0x800018ba. It retains actual dispatch, mixed-width
fetch and decoding, instruction execution, retirement, both clock choices
and restart through the reviewed Cycle rules. Its sole residual program
obligation is the unguarded ordinary next-cycle WP at the proved return
PC. This is a native NotStuck function-CPS theorem, not a termination,
concrete execution-witness or whole-kernel adequacy theorem. Generation
death continues to use the existing actual dead-thread rules.

Only one EntryConfig is supplied. Config derives every intermediate
fetch/interrupt/decoder/data/return requirement from source-supported
SupervisorConfig fields and the proved phase register projections. It
preserves arbitrary pending interrupts, external pins, initial nextPC,
clock/counter values, SATP ASID/PPN and unrelated register fields. Full
source MISA/MENVCFG, disabled SIE/delegation, MPRV=MXR=0, SXL=2, Bare SATP,
TOR entry-zero grant, disabled HTIF and actual pmaBoot are explicit inputs.
There is no per-instruction configuration, successful-read, trace or
state-preservation premise in either public contract.

Resources are the same 28 actual register cells, eleven separately framed
callee-saved cells (x9 and x18–x27), actual running context, discarded
34-byte native text span and two full context words at modular SP−8 and
SP−16. Geometry proves all 39 keys distinct and obtains each data window's
RAM range from the actual word assertion's alignment and first physical
byte. No extra SP-range or sixteen-byte alignment premise is added.

The two stores change the scratch words to entry RA and S0. Those same
linear byte/timestamp resources justify the later all-view reloads and
are returned with saved entry values. The caller's eleven cells are never
split out of the 28-cell bundle, duplicated or reallocated. Actual restart
returns reservation none after every cycle; initial reservation is
arbitrary. Fetch and data receipts are received, then affinely discharged
without claiming an ordering between them.

State/Reference are pure bookkeeping, not an alternative execution. They
prove all fourteen exact body projections and every actual Completed
clock successor preserves the next phase. PC arithmetic uses the true
2/4-byte widths, including AUIPC at mycpu+14. `reference_returned` also
checks the resulting off-clock register projection against the frozen
source-shaped MycpuRegisterSequence.returned. The private native chain
applies each real Cycle family rule before using its phase consequence;
it does not assume that the reference load values are returned by memory.

Result supplies both PC and nextPC equal to retPC(entry.RA), restored RA,
all thirteen callee-saved values, A0=mycpuRet(entry.TP), and unchanged
SupervisorConfig/stable control fields. Generic TP remains arbitrary;
the hart corollary explicitly assumes entry.TP=cpu.val and derives
A0.toNat=0x800123e8+128*cpu.val. It does not assume the source HartTp
invariant has been allocated. The continuation remains unguarded; the
fourteen internal rules retain their exact two/three guards.

Source mapping: pinned iris/ProofMycpu.v `MycpuProof.wp_mycpu_sconf`
(line 60) and SpecMycpu.v `wp_mycpu_sconf_body` (line 31), with the exact
CodeMycpu instructions and previously checked ELF/image/decoder facts.
This completes the Bare physical-resource body adaptation. Source
`ktier`, SIE/sconf capability, virtual free-stack recombination, KPT
translation and the caller's preceding JAL wrapper
`wp_call_mycpu_sconf_cs_body` (SpecMycpu.v:58) remain separate. No complete
source module-type implementation or original exported adequacy root is
claimed. The optional arbitrary-n physical stack corollary in the design
has not been added; both required public contracts use the exact two
actual full words.

Validation: `python3 tools/lake.py build Xv6.Kernel.MycpuBareLink` passed
721 jobs. State's fourteen-case kernel proof took 24s (local two-million
heartbeat budget); Reference 3.2s, Config 1s, Proofs 2.3s and Link 952ms.
Fresh physical-origin audit checked all 347 logical declarations across
all eight modules, including private declarations, types, opaque bodies
with allowOpaque=true and all constructor fields. Only propext,
Classical.choice and Quot.sound occur. One compiler-generated runtime
companion, reference._unsafe_rec, was verified to belong to the safe
structurally recursive reference definition and excluded as a runtime
root; no unsafe/partial declaration occurs anywhere in the logical cone.
There are no other exclusions and no sorry/native_decide/bv_decide.
Evidence: /tmp/xv6-lean-research/MycpuBareAudit.lean,
mycpu-bare-final-build.log, mycpu-bare-audit.log and
mycpu-bare-frozen.sha256. No previous owner file or umbrella was edited.

Fable's seventh review approves the native CPS without a soundness blocker.
The base eight-module snapshot is independently peer-audited; Fable reviewed
interfaces for several lower-level implementations omitted from its input.
Before declaring the Bare gate closed, a separate operational fourteen-cycle
witness is being constructed. A new reference_result lemma checks that the
bookkeeping final file satisfies the public Result; it is not the witness.

No allocation lemma currently produces the running context and register cells
for a supervisor EntryConfig. The existing allocate_shared_boot extracts the
34-byte code span and preserves the remaining boot clients; it does not prove
a supervisor entry setup or itself extract these two stack words. Separate
physical stack accessors support the latter. Resource-level entry inhabitation
remains a boot-path obligation. The rule is image-parametric under its supplied
resources; the intended pinned-xv6 instantiation is Xv6.Machine.bootImage.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
