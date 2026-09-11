# Configured Sv39 mycpu operational witness

This checkpoint defines a concrete operational witness, not boot reachability
or native Iris resource inhabitation. The artifact agent read all ten published
MycpuBareWitness modules, the shared pauseRun evaluator and its NodeSteps
soundness proof, and the actual generated Sv39 lookup/fill/translate path.
The new implementation will live exclusively under MycpuKptWitness; the
published Bare witness, generated model and existing native rules stay frozen.

The entry uses the same selected CPU3, TP3, PC0x800018ba, RA0x80000100,
SP0x80040000, S0x123456789abcdef0 and other hardware configuration as the
Bare witness. The platform fixes both reservation predicates false. Devices
are Devices.initial. The seven other hart register files are zero. The only
register configuration changes are exact Sv39 SATP
0x8000000000080050 (mode8, ASID0, rootPPN0x80050) and an explicit empty
64-entry TLB. False optional-clock choices and common view0 describe this
one permitted run; they do not restrict the actual machine relation.

Three complete page-table pages are overlaid on the actual loaded kernel RAM
in both initial memory and its TSO image:

| Physical page | Nonzero entry | Raw PTE meaning |
| --- | --- | --- |
| 0x80050000 | 2 | pointer to PPN0x80051, V only |
| 0x80051000 | 0 | pointer to PPN0x80052, V only |
| 0x80052000 | 1 | PPN0x80001, V/R/X/A/D |
| 0x80052000 | 63 | PPN0x8003f, V/R/W/A/D |

All other entries in all three pages are zero. The table words are encoded
into actual little-endian bytes; the image remains the original loaded RAM
everywhere else. These pages lie in the existing zero-filled RAM region and
are distinct from the code and the two stack save slots. U, G, PBMT, RSW and
reserved high bits are zero in this concrete fixture. Both leaves have A=D=1,
so actual PTE update logic requires no A/D memory writes despite the retained
source menvcfg value. Source general shared-KPT predicates are not assumed
or allocated by this setup.

The first instruction's actual fetch misses the TLB, performs the three-level
walk and fills index1 using Sv39Tlb.filled with the exact code PTE address
0x80052008. The first stack store in cycle2 similarly fills index63 using
PTE address0x800521f8. The remaining accesses hit these real entries.
Checkpoints retain the full dependent register file, using the existing
source-ordered pure body reference only as expected output bookkeeping,
with explicit minstret and actual expected TLB overlays. Every complete
generated-cycle equation must be kernel-checked; this expected reference
is not substituted for execution.

The image-parameterized write-pausing evaluator reuses the frozen
SpinlockWitness.pauseRun. Its generic soundness proof must take an actual
cache=image equality and then derive all read transitions from the real
Memory.read image/log/author/view. It accepts only actual ordinary RAM writes
with present values, appends the exact request snapshot, preserves metadata
and continuation, and clears the reservation exactly as NodeStep requires.
Unsupported events fail; merely stopping at an event supplies no progress.
No certificate will be interpreted as operational evidence until this
soundness proof is complete. The common-view/log bound is proved at every
recursive write. The actual code cache equality is reused from the Bare
witness and extended over the same three table pages.

The actual Defs/Spec checkpoint compiles in 728 jobs. Its sixteen fields cover
cache equality, initial checkpoint equality, every one of the 3*512 table
words, unchanged image outside the overlay, initial zero scratch words,
fourteen full generated-cycle equations, exact counted Cycles and joined
NodeSteps, final register Result, two real stack writes and counters,
unchanged all34 code bytes and all table bytes, arbitrary-address framing
outside the two stores, complete global frame, initial/final MemoryOK and
ReservationsOK, and positive execution in the actual twelve-thread
power :: powerFork0 pool. No caller-supplied successful execution or resource
inhabitation predicate is an input to the eventual closed Spec proof.

The result deliberately does not reuse MycpuBare.Result, whose configuration
requires Bare mode. The new Result instead retains exact full-file equality,
all source stable registers, all thirteen callee-saved registers, restored
RA/SP/S0, returned PC/nextPC, A0=mycpuRet(TP)=0x80012568, exact unchanged
Sv39 SATP and the two actual final TLB entries. The final state is the actual
selected-hart writeBack; its device equality includes the whole durable disk.
The log has only the two real stack saves, and all twelve workers remain
present while only CPU3 is scheduled. Reaching the return address does not
claim executing the caller's next instruction.

After interface approval: prove generic evaluator soundness and image/table
facts, then kernel certificates in bounded shards, full register-order
normalization, final resource-free results and memory frames, and actual
pool lifting/positive step count. Audit all physical declarations and complete
type/opaque/constructor cones. There will be no native_decide, custom axiom,
unsafe/partial code or generated-model edit. The proof-only evaluator is
noncomputable so Lean emits no unsafe recursion companion. Every physical
declaration is audited, with zero exclusions.

This can close an operational half of a later translated-function milestone.
It does not prove the source native SConf/KPT capability inhabitation,
publication premises, configured-state boot reachability, translated native
function WP, cross-prover correspondence or any of the six whole-system roots.

Implementation checkpoint: all ten modules are now frozen after a 738-job
build. The compact full-file bridge compiles in10s, the two actual-cycle
certificate shards in10s/11s and final assembly in814ms. All222 physical
declarations passed the full type/opaque/constructor audit with zero
exclusions and no unsafe/partial dependency. The sixteen approved contracts and all scope
limits above remain unchanged. See MycpuKptWitnessSTATUS.md for exact
proof roles and evidence. No native or boot inhabitation is inferred.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
